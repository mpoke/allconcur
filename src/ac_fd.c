/**                                                                                                      
 * AllConcur
 * 
 * Failure detector
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <debug.h>

#include <allconcur.h>
#include <ac_ep.h>
#include <ac_fd.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define FD_BUF_SIZE 16384 // 16KiB


#define FD_MSG_HB_REQ	1
#define FD_MSG_HB		2
#define FD_MSG_STOP	    3
#define FD_MSG_STOP_ACK	4

struct fd_msg_t {
    uint64_t sqn;
    uint32_t sid;
	uint8_t type;
    uint8_t padding[3];
}; 
typedef struct fd_msg_t fd_msg_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

struct ev_loop *fd_loop;            /* loop for EV library: FD thread */
ev_timer w_send_hb;
ev_timer w_timeout;
ev_idle fd_w_poll;

uint64_t hb_sqn;

char epstr[EPSTR_LEN];

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

void static 
fd_terminate(int rc);

static fd_ep_t*
fd_find_endpoint(fd_ep_t *head, void *endpoint);
static void
fd_rm_endpoint(fd_ep_t **head, void *endpoint);

static void
send_hb_cb(EV_P_ ev_timer *w, int revents);

static void
send_hb_cb(EV_P_ ev_timer *w, int revents);
static void
timeout_cb(EV_P_ ev_timer *w, int revents);
static void
fd_poll_cb(EV_P_ ev_idle *w, int revents);

#endif

/* ================================================================== */
/* Global functions */
#if 1

/**
 * Failure Detector
 * 
 * Brief description:
 * When a server connects to a successor, it sends a hello message 
 * that contains info about the UD endpoint; the successor adds the 
 * server to the list of monitored servers (i.e., data.fd.prev_srv); 
 * for each new monitored server, a FD_MSG_HB_REQ message is sent 
 * (request for HBs).
 *
 * When receiving an HB request, a new endpoint is added to the list of 
 * successors (i.e., data.fd.next_srv) 
 * 
 * TODO: If a server fails before connecting to its successors, 
 * it will never be monitored -> no failure detection.
 */
void *failure_detector()
{        
    int rv; 
    
    pthread_mutex_lock(&data.fd.next_mutex);
    fd_loop = ev_loop_new(EVFLAG_AUTO);
    if (NULL == fd_loop) {
        data.fd.error = 1;
        pthread_cond_signal(&data.fd.cond);
        pthread_mutex_unlock(&data.fd.next_mutex);
        fd_error("ev_loop_new\n");
        fd_terminate(1);
    }

    /* Set up datagram transfer (FD) */
    memcpy(data.fd.ud.cd.ei.host, data.self_ni.host, 
                sizeof data.self_ni.host);
    memcpy(data.fd.ud.cd.ei.port, data.self_ni.fd_port, 
                sizeof data.self_ni.fd_port);
    data.fd.ud.cd.rcount = data.outstanding;
    data.fd.ud.cd.scount = data.outstanding;
    data.fd.ud.cd.rbuf_len = 0, // set directly to MTU
    data.fd.ud.cd.sbuf_len = 0, // set directly to MTU
    data.fd.ud.cd.handle_data = handle_fd_data;
    rv = ac_net_mod->ud_setup(&data.fd.ud);
    if (rv) {
        data.fd.error = 1;
        pthread_cond_signal(&data.fd.cond);
        pthread_mutex_unlock(&data.fd.next_mutex);
        error("ud_setup\n");
        fd_terminate(1);
    }
    pthread_cond_signal(&data.fd.cond);
    pthread_mutex_unlock(&data.fd.next_mutex);
    
    char epstr[EPSTR_LEN];
    fd_info_wtime("Local UD info: %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, data.fd.ud.ud_info.endpoint));

    /* Initialize and start a timer watcher for timing out */
    ev_timer_init(&w_timeout, timeout_cb, 0., data.fd.timeout);
    ev_set_priority(&w_timeout, EV_MAXPRI-3);
    ev_timer_again(fd_loop, &w_timeout);
    
    /* Initialize and start a timer watcher for sending HBs */
    ev_timer_init(&w_send_hb, send_hb_cb, 0., NOW);
    ev_set_priority(&w_send_hb, EV_MAXPRI-2);
    ev_timer_again(fd_loop, &w_send_hb);
    
    /* Init the poll event */
    ev_idle_init(&fd_w_poll, fd_poll_cb);
    ev_set_priority(&fd_w_poll, EV_MAXPRI);
    ev_idle_start(fd_loop, &fd_w_poll);

    /* Start loop */
    ev_run(fd_loop, 0);

    pthread_exit(NULL);
}

void handle_fd_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    int rv;
    fd_msg_t *msg;
    fd_ep_t *ep;
    
    if (!endpoint) {
        fd_error("endpoint is NULL\n");
        fd_terminate(1);
    }
    if (!recv_buf) {
        fd_error("recv_buf is NULL\n");
        fd_terminate(1);
    }
    
    msg = (fd_msg_t*)recv_buf;

    int pid;

    switch (msg->type) {
    case FD_MSG_HB_REQ:
    {
        /* Request for HBs -- add to list of successors */
#ifdef FD_INFO 
fd_info_wtime("Receive HB-REQ from %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, endpoint));
#endif
        pthread_mutex_lock(&data.fd.next_mutex);
        ep = fd_add_endpoint(&data.fd.next_srv, endpoint);
        if (!ep) {
            pthread_mutex_unlock(&data.fd.next_mutex);
            fd_error("fd_add_endpoint\n");
            fd_terminate(1);
        }
        ep->sqn = msg->sqn;
        ep->sid = msg->sid;
        ep->state = FD_EP_NEW;
#ifdef FD_INFO 
fd_info_wtime("New successor\n");
fd_print_endpoints(data.fd.next_srv);
fd_info("   # start sending HB to p%"PRIu32"\n\n", msg->sid);
#endif
        pthread_mutex_unlock(&data.fd.next_mutex);
        w_send_hb.repeat = NOW;
        ev_timer_again(fd_loop, &w_send_hb);
        break;
    }
    case FD_MSG_HB:
    {
        /* Received HB */
#ifdef FD_DEBUG
fd_info_wtime("Receive HB from %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, endpoint));
#endif
        pthread_mutex_lock(&data.fd.prev_mutex);
        ep = fd_find_endpoint(data.fd.prev_srv, endpoint);
        if (ep) {            
            ep->hb++;
            ep->hb_tstamp = ev_now(fd_loop);
            /* Mark server as active: it knows that I'm monitoring it */
            ep->state = FD_EP_ACTIVE;          
        }
        pthread_mutex_unlock(&data.fd.prev_mutex);
        break;
    }
    case FD_MSG_STOP:
    {
        /* Received notification to stop monitoring */
#ifdef FD_INFO 
fd_info_wtime("Receive STOP from %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, endpoint));
#endif
        pthread_mutex_lock(&data.fd.prev_mutex);
        fd_rm_endpoint(&data.fd.prev_srv, endpoint);
        pthread_mutex_unlock(&data.fd.prev_mutex);
        /* Send back ACK */
        fd_msg_t reply;
        memset(&reply, 0, sizeof reply);
        reply.type = FD_MSG_STOP_ACK;
        rv = ac_net_mod->sendto(&data.fd.ud, endpoint, &reply, sizeof reply);
        if (rv) {
            fd_error("sendto\n");
            fd_terminate(1);
        }
        break;
    }
    case FD_MSG_STOP_ACK:
    {
        /* Received ACK of stop monitoring notification */
#ifdef FD_INFO 
fd_info_wtime("Receive STOP-ACK from %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, endpoint));
#endif
        pthread_mutex_lock(&data.fd.next_mutex);
        fd_rm_endpoint(&data.fd.next_srv, endpoint);
        pthread_mutex_unlock(&data.fd.next_mutex);
        break;
    }
    default:
        fd_error("Received unknown message\n");
        fd_terminate(1);
    }
}

void fd_rm_ep(fd_ep_t **head, fd_ep_t *fd_ep)
{
    if (!fd_ep) return;
    if (fd_ep->next) {
        fd_ep->next->prev = fd_ep->prev;
    }
    if (fd_ep->prev) {
        fd_ep->prev->next = fd_ep->next;
    }
    if (*head == fd_ep) {
        (*head) = fd_ep->next;
    }
    if (fd_ep->endpoint) {
        free(fd_ep->endpoint);
    }
    free(fd_ep);
}

fd_ep_t* fd_add_endpoint(fd_ep_t **head, void *endpoint)
{
    int rv;
    fd_ep_t *ep, *prev = NULL;
    //fd_info_wtime("Adding endpoint %s\n", 
    //        ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, endpoint));
    
    if (!head) {
        fd_error("head is NULL\n");
        return NULL;
    }
    ep = *head;
    while (ep) {
        if (ac_net_mod->cmp_ud_eps(ep->endpoint, endpoint) == 0) {
            break;
        }
        prev = ep;
        ep = ep->next;
    }
    if (ep) {
        return ep;
    }
    
    ep = (fd_ep_t*)malloc(sizeof(fd_ep_t));
    if (!ep) {
        fd_error("malloc\n");
        return NULL;
    }
    memset(ep, 0, sizeof(fd_ep_t));
    ep->state = FD_EP_NEW;
    ep->hb_tstamp = ev_now(fd_loop);
    rv = ac_net_mod->cp_ud_ep(&ep->endpoint, endpoint);
    if (rv) {
        fd_error("cp_ud_ep\n");
        return NULL;
    }
    
    if (prev) {
        prev->next = ep;
        ep->prev = prev;
    }
    else {
        *head = ep;
    }
    
    return ep;
}

void fd_print_endpoints(fd_ep_t *head)
{
    fd_ep_t *ep;
    if (!head) {
        return;
    }
    ep = head;
    while (ep) {
        fd_info("   %s\n", 
            ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
        ep = ep->next;
    }
    
}

void fd_stop()
{
    /* Acquire lock */
    pthread_mutex_lock(&data.fd.next_mutex);
    
    data.fd.stop_sending = 1;
    
    /* Release lock */
    pthread_mutex_unlock(&data.fd.next_mutex);
}

void fd_start()
{
    /* Acquire lock */
    pthread_mutex_lock(&data.fd.next_mutex);
    
    data.fd.stop_sending = 0;
    
    /* Release lock */
    pthread_mutex_unlock(&data.fd.next_mutex);
}


#endif

/* ================================================================== */
/* Local functions */
#if 1

void static 
fd_terminate(int rc)
{   
    fd_ep_t *ep;
        
    info_wtime("Stop detecting failures\n");

    if (fd_loop) {
        /* Close poll watcher */
        ev_idle_stop(fd_loop, &fd_w_poll);
    
        /* Stop the timer watcher used for sending HBs */
        ev_timer_stop(fd_loop, &w_send_hb);
    
        /* Stop the timer watcher used for timing out */
        ev_timer_stop(fd_loop, &w_timeout);
    
        /* Terminate loop event */
        ev_break(fd_loop, EVBREAK_ONE); 
        ev_loop_destroy(fd_loop);
    }

    /* Free list of FD successors */
    pthread_mutex_lock(&data.fd.next_mutex);
    ep = data.fd.next_srv;
    while (NULL != (ep = data.fd.next_srv)) {
        data.fd.next_srv = ep->next;
        if (ep->endpoint) {
            free(ep->endpoint);
        }
        free(ep);
    }
    pthread_mutex_unlock(&data.fd.next_mutex);   
    
    /* Free list of FD predecessors */
    pthread_mutex_lock(&data.fd.prev_mutex);
    ep = data.fd.prev_srv;
    while (NULL != (ep = data.fd.prev_srv)) {
        data.fd.prev_srv = ep->next;
        if (ep->endpoint) {
            free(ep->endpoint);
        }
        free(ep);
    }
    pthread_mutex_unlock(&data.fd.prev_mutex);
    
#ifdef FD_INFO 
    fd_info_wtime("[FD] done\n");
#endif
    
    pthread_exit(NULL);
}

static fd_ep_t*
fd_find_endpoint(fd_ep_t *head, void *endpoint)
{
    fd_ep_t *ep;
    if (!head) {
        return NULL;
    }
    ep = head;
    while (ep) {
        if (ac_net_mod->cmp_ud_eps(ep->endpoint, endpoint) == 0) {
            break;
        }
        ep = ep->next;
    }
    
    return ep;    
}

static void
fd_rm_endpoint(fd_ep_t **head, void *endpoint)
{
    fd_ep_t *ep;
    if (!head) {
        fd_error("head is NULL\n");
        fd_terminate(1);
    }
    ep = *head;
    while (ep) {
        if (ac_net_mod->cmp_ud_eps(ep->endpoint, endpoint) == 0) {
            break;
        }
        ep = ep->next;
    }
    fd_rm_ep(head, ep);
}

/**
 * Periodically send HBs
 */
static void
send_hb_cb(EV_P_ ev_timer *w, int revents)
{
    int rv;
    static int count = 0;
    static int init = 0;
    fd_ep_t *ep;
    srv_t *srv;
    fd_msg_t msg;

    HRT_TIMESTAMP_T t1, t2;
    uint64_t ticks;
    double usecs;
    
    memset(&msg, 0, sizeof msg);
    msg.sqn = hb_sqn++;
    
    pthread_mutex_lock(&data.fd.next_mutex);
    
    if (data.fd.stop_sending) {
        pthread_mutex_unlock(&data.fd.next_mutex);
        goto rearm;
    }
    
    /* Send HB to all successors */
    ep = data.fd.next_srv;
    while (ep) {
        if (FD_EP_OLD == ep->state) {
            /* Send request to stop expecting HBs */
			msg.type = FD_MSG_STOP;
		}
		else if (FD_EP_NEW == ep->state) {
            /* Send HB */
			msg.type = FD_MSG_HB;
            ep->state = FD_EP_ACTIVE;     
#ifdef FD_DEBUG           
            fd_info_wtime("Send HB to %s\n", 
                ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
#endif            

        }
        else {
#if 0            
            srv = &data.vertex_to_srv_map[ep->sid];
            if ((srv->sqn == ep->sqn) && srv->sent_data) {
                srv->sent_data = 0;
                goto next_successor;
            }
#endif            
            /* Send HB */
			msg.type = FD_MSG_HB;     
#ifdef FD_DEBUG           
            fd_info_wtime("Send HB to %s\n", 
                ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
#endif            
		}
        rv = ac_net_mod->sendto(&data.fd.ud, ep->endpoint, &msg, sizeof msg);
        if (rv) {
            fd_error("sendto\n");
            fd_terminate(1);
        }
next_successor:        
        ep = ep->next;
    }
    
    /* Release lock */
    pthread_mutex_unlock(&data.fd.next_mutex);
    
    if (!timer) goto rearm;

    count++;
    if (count == 10) {
        if (!init) {
            init = 1;
            goto rearm;
        }
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        usecs = HRT_GET_USEC(ticks);
#ifdef FD_DEBUG           
        fd_info_wtime("Sent %d HB in %lf usecs (%lf)\n", count, usecs, (count/usecs)*data.fd.timeout*1e6);
#endif        
#ifdef FD_INFO 
        double mean = (count/usecs)*(1.0*data.fd.timeout*1e6);
        if (mean < 0.7*(data.fd.timeout/data.fd.hb_period)) {
            fd_info_wtime("not sending enough HB within a timeout: %lf\n", mean);
        }
#endif        
        HRT_GET_TIMESTAMP(t1);
        count = 0;
    }
    
rearm:    
    /* Rearm timer */
    w->repeat = data.fd.hb_period;
    ev_timer_again(EV_A_ w);
}

/**
 * Periodically check whether the predecessors sent HBs
 */
static void
timeout_cb(EV_P_ ev_timer *w, int revents)
{
    int rv;
    fd_ep_t *ep, *next;
    srv_t *srv;
    fd_msg_t msg;
    memset(&msg, 0, sizeof msg);
    
    w->repeat = 0;
    ev_timer_again(EV_A_ w);

    /* Acquire lock */
    pthread_mutex_lock(&data.fd.prev_mutex);
    
    /* Check all predecessors */
    ep = data.fd.prev_srv;
    while (ep) {
        next = ep->next;
        srv = &data.vertex_to_srv_map[ep->sid];
        if (FD_EP_NEW == ep->state) {
			/* New server; send HB_REQ... */
            msg.type = FD_MSG_HB_REQ;
            msg.sqn = data.vertex_to_srv_map[data.self].sqn;
            msg.sid = data.self;
            rv = ac_net_mod->sendto(&data.fd.ud, ep->endpoint, &msg, sizeof msg);
            if (rv) {
                fd_error("sendto\n");
                fd_terminate(1);
            }
#ifdef FD_INFO 
fd_info_wtime("Send HB-REQ to p%"PRIu32": %s\n",
            ep->sid, ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
#endif
			/* ...and check whether the warmup period was exceeded */
			if (ev_now(EV_A) - ep->hb_tstamp > data.fd.warmup) {
				/* No HB in the last warmup period */
#ifdef FD_INFO 
fd_info_wtime("!!! p%"PRIu32" failed: %s -- warmup period over\n", ep->sid,
                ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
#endif
				goto failure;
			}
        }
#if 1        
        else if ((srv->sqn == ep->sqn) && srv->received_data) {
            srv->received_data = 0;
            ep->rounds++;
            ep->total_hb += ep->hb;
//            if (ep->hb == 0) {
//fd_info_wtime("!!! p%"PRIu32" whould have failed: %s\n", ep->sid,
 //               ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
 //           }
            ep->hb = 0; 
        }
#endif        
        else if (FD_EP_OLD == ep->state) {
			/* No longer a predecessor -- remove */
            fd_rm_ep(&data.fd.prev_srv, ep);
		}
        else if (FD_EP_FAILED == ep->state) {
			/* Already failed */
		}
		else {
            ep->rounds++;
            ep->total_hb += ep->hb;
            if (ep->hb == 0) {
#ifdef FD_INFO 
fd_info_wtime("!!! p%"PRIu32" failed: %s\n", ep->sid,
                ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
fd_info("   on avarage per round: %lf\n", 1.*ep->total_hb/ep->rounds);
#endif
                goto failure;
            }
            ep->hb = 0; 
#if 0            
			if (now - ep->hb_tstamp > data.fd.timeout) {
				/* No HB in the last timeout period */
				goto failure;
			}
#endif
		}
        ep = next;
        continue;
failure:
        /* Server failed */
        ep->state = FD_EP_FAILED;
        data.fd.failure++;
        ep = next;
    }
    
    /* Release lock */
    pthread_mutex_unlock(&data.fd.prev_mutex);
    
    /* Rearm timer */
    w->repeat = data.fd.timeout;
    ev_timer_again(EV_A_ w);
}

static void
fd_poll_cb(EV_P_ ev_idle *w, int revents)
{
    int rv;
    if (quit(&data.quit_mutex)) {
#ifdef FD_INFO 
        fd_info_wtime("local server terminated\n");
#endif        
        fd_terminate(0);
    }
    
    /* Poll completion of sendto operations */
    if (ac_net_mod->poll_sendto) {
        rv = ac_net_mod->poll_sendto(&data.fd.ud);
        if (rv) {
            fd_error("poll_sendto\n");
            fd_terminate(1);
        }
    }
    
    /* Poll completion of recv operations */
    if (ac_net_mod->ud_poll_recv) {
        rv = ac_net_mod->ud_poll_recv(&data.fd.ud);
        if (rv) {
            fd_error("ud_poll_recv\n");
            fd_terminate(1);
        }
    }
}

#endif
