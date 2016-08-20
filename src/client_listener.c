/**                                                                                                      
 * AllConcur 
 * 
 * Client listener
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
#include <client_listener.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define READ_CMD        1
#define READ_DATA       2

struct cl_reply_t {
    uint32_t in;
    shared_buf_t *sh_buf;
    struct cl_reply_t *next, *prev;
};
typedef struct cl_reply_t cl_reply_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

struct ev_loop *cl_loop;            /* loop for EV library: cl thread */
ev_idle cl_w_poll;
ev_timer w_iamalive;

uint32_t client_count = 0;
cl_reply_t *reply_head = NULL, *reply_tail = NULL;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void
iamalive_cb(EV_P_ ev_timer *w, int revents);
void static 
cl_terminate(int rc);
static int
cl_send_replies();
static void* 
new_client(void *conn);
static void 
handle_client_data(void *endpoint, void *recv_buf, uint32_t recv_len);
static void
cl_poll_cb(EV_P_ ev_idle *w, int revents);


#endif

/* ================================================================== */
/* Global functions */
#if 1

void *wait_for_clients()
{
    struct addrinfo hints, *servinfo, *p;
    int yes=1;
    int rv;
    /* Listen for connection from clients */
    conn_data_t conn_data = {
        .rcount = 2,
        .scount = 2,
        .rbuf_len = data.max_buf_size / data.outstanding,
        .sbuf_len = data.max_buf_size / data.outstanding,
        
        .on_connection = new_client,
        .destroy_ep_data = ac_destroy_client,
        .handle_data = handle_client_data,
    };
    memcpy(conn_data.ei.port, data.clt_port, sizeof(data.clt_port));
    data.client_ch = ac_net_mod->ilisten(&conn_data);
    if (NULL == data.client_ch) {
        error("ilisten\n");
        cl_terminate(1);
    }
    
    /* Publish listening port */
    char filename[NAME_MAX];
    sprintf(filename, "srv_%s#%s.clt", data.self_ni.host, data.self_ni.ac_port);
    FILE *stream = fopen(filename, "w+");
    fprintf(stream, "%s\n", conn_data.ei.port);
    fclose(stream);
    
    cl_loop = ev_loop_new(EVFLAG_AUTO);
    if (NULL == cl_loop) {
        error("ev_loop_new\n");
        cl_terminate(1);
    }

    /* Init the poll event */
    ev_idle_init(&cl_w_poll, cl_poll_cb);
    ev_set_priority(&cl_w_poll, EV_MAXPRI);
    ev_idle_start(cl_loop, &cl_w_poll);
        
    //ev_timer_init(&w_iamalive, iamalive_cb, 0., 0.1);
    //ev_set_priority(&w_iamalive, EV_MAXPRI-1);
    //ev_timer_again(cl_loop, &w_iamalive);

    /* Start loop */
    ev_run(cl_loop, 0);

    pthread_exit(NULL);
}

int cl_add_reply(uint32_t in, shared_buf_t *sh_buf)
{
    cl_reply_t *reply = (cl_reply_t*)malloc(sizeof(cl_reply_t));
    if (!reply) {
        error("malloc (%s)\n", strerror(errno));
        return 1;
    }
    memset(reply, 0, sizeof(cl_reply_t));
    reply->in = in;
    reply->sh_buf = sh_buf;
    
    pthread_mutex_lock(&data.clt_mutex);
    if (reply_tail) {
        reply_tail->next = reply;
        reply->prev = reply_tail;
        reply_tail = reply;
    }
    else {
        reply_tail = reply;
        reply_head = reply;
    }
    pthread_mutex_unlock(&data.clt_mutex);
    
    return 0;
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static void
iamalive_cb(EV_P_ ev_timer *w, int revents)
{
    info_wtime("I am alive\n");
}

static void
cl_terminate(int rc)
{   
    cl_reply_t *reply;
 
    info_wtime("Stop listening to clients\n");
    
    if (cl_loop) {
        /* Close poll watcher */
        ev_idle_stop(cl_loop, &cl_w_poll);
    
        /* Terminate loop event */
        ev_break(cl_loop, EVBREAK_ONE); 
        ev_loop_destroy(cl_loop);
    }

    pthread_mutex_lock(&data.clt_mutex);
    while (reply_head) {
        reply = reply_head;
        reply_head = reply_head->next;
        if (!reply->sh_buf->shared_count) {
            free(reply->sh_buf);
        }
        free(reply);
    }
    pthread_mutex_unlock(&data.clt_mutex);

    pthread_exit(NULL);
}

static int
cl_send_replies()
{
    int rv;
    ep_t *ep;
    client_t *client;
    cl_reply_t *reply;
    
    if (!reply_head) return 0;

pop_reply:
    pthread_mutex_lock(&data.clt_mutex);
    if (!reply_head) {
        pthread_mutex_unlock(&data.clt_mutex);
        return 0;
    }
    reply = reply_head;
    reply_head = reply_head->next;
    if (!reply_head) reply_tail = NULL;
    pthread_mutex_unlock(&data.clt_mutex);
    
    ep = data.client_list;    
    while (NULL != ep) {
        if (ep->data) {
            client = (client_t*)ep->data;
//info("Client %"PRIu64"-%"PRIu64": in = %"PRIu32"\n", client->cmd.cid.srv_sqn, client->cmd.cid.clt_sqn, client->in);
            if (client->in == reply->in) {
                break;
            }
        }
        ep = ep->next;
    } 
    if (NULL == ep) {
        /* Cannot find client */
        error("Cannot find client\n");
        goto free_reply;
    }
    /* Reset the client->in index */
    client->in = UINT32_MAX;
           
    /* Send the message (asynch) */
    rv = ac_net_mod->isend(ep, reply->sh_buf);
    if (rv) {
        error("isend\n");
        goto exit_with_error;
    }
    if (!reply->sh_buf->shared_count) {
        free(reply->sh_buf);
    }
    rv = 0;
free_reply:
    if (reply)
        free(reply);
    goto pop_reply;
exit_with_error:
    if (reply)
        free(reply);
    return 1;
}

static void* 
new_client(void *conn)
{
    info_wtime("New client connected\n");
    
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = (ep_t*)malloc(sizeof(ep_t));
    if (NULL == ep) {
        error("malloc (%s)\n", strerror(errno));
        return NULL;
    }
    memset(ep, 0, sizeof(ep_t));
    ep->conn = conn;
    ep->connected = 1;
    conn_ctx->ep = ep;
    conn_ctx->buffering = 1;
    
    ep->data = malloc(sizeof(client_t));
    if (NULL == ep->data) {
        error("malloc (%s)\n", strerror(errno));
        free(ep);
        return NULL;
    }
    client_count++; 
    client_t *client = (client_t*)ep->data;
    memset(client, 0, sizeof(client_t));
    client->state = READ_CMD;
    client->buf = (uint8_t*)&client->cmd;
    
    ep->head = &data.client_list;
    ac_ep_add(ep);    
    return ep;
}

static void 
handle_client_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    int direct_cp, rv;
    uint32_t len, idx;
    kvs_ht_reply_t reply;
    void *req_data;
    shared_buf_t *sh_buf;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        cl_terminate(1);
    }
    client_t *client = (client_t*)ep->data;
    if (!client) {
        error("client is NULL\n");
        cl_terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        cl_terminate(1);
    }
    
    while (recv_len != 0) {
        direct_cp = 0;
        if (READ_CMD == client->state) {
            /* Receiving a command from a client */
            len = sizeof(kvs_ht_cmd_t) - client->byte_count;
            if (recv_len < len) {
                /* partially */
                memcpy(client->buf, recv_buf, recv_len);
                client->buf += recv_len;
                client->byte_count += recv_len;
                return;
            }
            /* complete */
            memcpy(client->buf, recv_buf, len);
            recv_buf += len;
            recv_len -= len;
        }
        else if (READ_DATA == client->state) {
            goto copy_data;
        }
        else {
            error("unknown state\n");
            cl_terminate(1);
        }
        
        /* Received CMD header; now read data */
        client->state = READ_DATA;
        if (CTRL_JOIN == client->cmd.type) {
            /* JOIN request -- need to read net_id_t */
            info_wtime("Received JOIN request\n");
            len = sizeof(net_id_t); 
        }
        else {
            /* SM CMD -- need to read key and value */       
            len = client->cmd.key_len + client->cmd.value_len;
        }
        if (len <= recv_len) {
            direct_cp = 1;
            goto got_data;
        }
        /* Need to copy data into buffer - is there enough space? */
        if (client->data_len != len) {
            /* Reallocate input */
            client->data = realloc(client->data, len);
            if (NULL == client->data) {
                error("allocating data buffer\n");
                cl_terminate(1);
            }
            client->data_len = len;
        }
        client->buf = client->data;
        client->byte_count = 0;
        
copy_data:
        len = client->data_len - client->byte_count;
        if (recv_len < len) {
            /* partially */
            memcpy(client->buf, recv_buf, recv_len);
            client->buf += recv_len;
            client->byte_count += recv_len;
            return;
        }
        /* complete */
        memcpy(client->buf, recv_buf, len);
        recv_buf += len;
        recv_len -= len;

got_data:
        /* Completely received the request */
        if (client->wip) {
            /* Already handling a request */
            memset(&reply, 0, sizeof(kvs_ht_reply_t));
            reply.type = REPLY_WIP;
            goto send_reply;
        }
        if (direct_cp) {
            req_data = recv_buf;
            recv_buf += len;
            recv_len -= len;
        }
        else {
            req_data = client->data;
            len = client->data_len;
        }
        /* Add request to the request pool */
        rv = rp_add_request(&data.request_pool,  
                            &(client->cmd), sizeof(kvs_ht_cmd_t),
                            req_data, len, &client->in);
        info_wtime("New client request added in round #%"PRIu64"\n", 
                    consensus_sqn);            
        if (RP_FULL == rv) {
            /* Not enough space for this request */
            memset(&reply, 0, sizeof(kvs_ht_reply_t));
            reply.type = REPLY_FULL;
            goto send_reply;
        }
        /* Mark request as WIP */
        //client->wip = 1;
        
reset_state:    
        /* Reset state so that we can receive new requests */    
        client->state = READ_CMD;
        client->buf = (uint8_t*)&client->cmd;
        client->byte_count = 0;
        continue;
    
send_reply:
        len = sizeof(shared_buf_t) + sizeof(kvs_ht_reply_t);
        sh_buf = (shared_buf_t*)malloc(len);
        if (NULL == sh_buf) {
            error("malloc (%s)\n", strerror(errno));
            cl_terminate(1);
        }
        memset(sh_buf, 0, len);
        sh_buf->len = len - sizeof(shared_buf_t);
        memcpy(sh_buf->buf, &reply, sizeof(kvs_ht_reply_t));
        rv = ac_net_mod->isend(ep, sh_buf);
        if (rv) {
            error("malloc (%s)\n", strerror(errno));
            cl_terminate(1);
        }
        if (!sh_buf->shared_count) {
            free(sh_buf);
            sh_buf = NULL;
        }
        goto reset_state;
    }
}

static void
cl_poll_cb(EV_P_ ev_idle *w, int revents)
{
    int rv; 
    ep_t *ep;
    
    if (quit(&data.quit_mutex)) {
        cl_terminate(1);
    }
    
    /* Poll for incoming connections (from clients) */
    if (ac_net_mod->poll_ch) {
        rv = ac_net_mod->poll_ch(data.client_ch);
        if (rv) {
            error("poll_ch\n");
            cl_terminate(1);
        }
    }
    
    /* Poll for data from predecessors */
    if (ac_net_mod->poll_recv) {
        ep = data.client_list;
        while (NULL != ep) {
            rv = ac_net_mod->poll_recv(ep);
            if (rv) {
                error("poll_recv\n");
                cl_terminate(1);
            }            
            ep = ep->next;
        }
    }
    
    rv = cl_send_replies();
    if (rv) {
        error("cl_send_replies\n");
        cl_terminate(1);
    } 
    
    /* Poll completion of send operations */
    if (ac_net_mod->poll_send) {
        ep = data.client_list;
        while (NULL != ep) {
            if (ep->connected) {
                rv = ac_net_mod->poll_send(ep);
                if (-1 == rv) {
                    error("poll_send\n");
                    cl_terminate(1);
                }            
            }
            ep = ep->next;
        }
    }
    
}

#endif 
