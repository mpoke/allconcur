/**                                                                                                      
 * AllConcur
 * 
 * The algorithm
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <unistd.h>
#include <debug.h>

#include <allconcur.h>
#include <messages.h>


#include <ac_types.h>
#include <ac_init.h>
#include <ctrl_sm.h>
#include <client_listener.h>
#include <ac_algorithm.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define WARMUP_COUNT 10

//#define BW_BENCH


#define READ_MSG        1
#define READ_IN         2
#define READ_HELLO      3
#define READ_UDINFO     4
#define READ_UDINFO_LEN 5
#define READ_MTU        6

#define FAIL_RANDOM 1
#define FAIL_CHAIN  2


#ifdef BENCHMARK

#define WW_WORK 0
#define WW_WAIT 1
#define WW_INIT 2
#define WW_NONE 3

#define BENCH_BUF_LEN 8192

struct bench_round_data_t {
    uint64_t round_sqn;
    double usecs;
    double wait, work;
    uint32_t srv_count;
    uint32_t byte_count;
    double rx_bw, tx_bw;
};
typedef struct bench_round_data_t bench_round_data_t;

struct bench_buf_round_t {
    struct bench_buf_round_t *next;
    bench_round_data_t buf[BENCH_BUF_LEN];
    uint32_t idx;
};
typedef struct bench_buf_round_t bench_buf_round_t;

struct bench_buf_double_t {
    struct bench_buf_double_t *next;
    double buf[BENCH_BUF_LEN];
    uint32_t idx;
};
typedef struct bench_buf_double_t bench_buf_double_t;

struct bench_data_t {
    uint32_t srv_count; 
    uint32_t msg_count; /* number of non empty messages agreed upon */
    uint32_t byte_count;

    bench_buf_round_t *round_head, *round_tail;
#ifdef MSG_DELAY    
    bench_buf_double_t *delay_head, *delay_tail;
#endif    
    bench_buf_double_t *throughput_head, *throughput_tail;
    bench_buf_double_t *request_head, *request_tail;
};
typedef struct bench_data_t bench_data_t;
bench_data_t bench_data;
#endif

#endif

/* ================================================================== */
/* Global variables */
#if 1

/* Sample size:
 * ignored for failure benchmark 
 * # allconcur rounds for latency benchmark
 * # throughput measurements else
 */
const int sample_size = 1000;

uint64_t consensus_sqn;

int successor_count = 0;

const double timeout = 0.02;

#ifdef BENCHMARK 
int warmup;

/* Timer watcher for generating requests */
ev_timer w_add_request;

/* Timer watcher for measuring throughput */
ev_timer w_throughput;
double throughput_out_period = 0.1; // in seconds
uint32_t agreed_on_byte_count;
uint32_t throughput_rounds = 1;

kvs_ht_cmd_t *request = NULL;

int failure_scenario = FAIL_RANDOM;
//~ int failure_scenario = FAIL_CHAIN;
uint8_t *faulty_servers;
uint8_t fail_round = 0;
uint32_t fail_count = 1;
uint32_t wait_for_message;
uint32_t last_msg_recv;
uint32_t send_message_to;
uint32_t failing_point;
uint8_t failed;
uint64_t iterations=0;
uint64_t start_hb_sqn = 0;
int repeat_round=5;

int bench_done;

uint32_t batching_factor = 1;
//uint32_t batching_factor = 512;
//const uint32_t max_req_count = 2048;
//const uint32_t max_req_count = 4096;
//const uint32_t max_req_count = 1;

HRT_TIMESTAMP_T t_round_start, t_round_end;
HRT_TIMESTAMP_T tww[2];
double ww_usecs[2], send_usecs;
int ww_flag = WW_NONE;
uint64_t recv_bytes, sent_bytes;
uint32_t avoid_redundant_count = 0;

int msg_received;
#endif

int handling_premature_msgs = 0;

#ifdef BW_BENCH
int started_timer = 0;
int bw_bench_done = 0;
int warmup_done = 0;
#endif



#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void
handle_message(message_t *msg, uint32_t from_sid);
static void 
handle_failure_notification(uint32_t pj, uint32_t pk);
static void
handle_input(uint32_t pj, uint32_t inlen, uint32_t from_sid);
static void 
send_message_further(message_t *msg, uint32_t send_idx, uint32_t from_sid);
static void 
send_failure_notification(uint32_t sid);

static void 
check_join_requests();
static int
reply_to_client(uint32_t offset, shared_buf_t *sh_buf);

static void 
remove_server(uint32_t sid);
static void
print_failure_notifications(uint32_t sid);

static void
terminate_cb(EV_P_ ev_timer *w, int revents);

#ifdef BENCHMARK 
static void
throughput_cb(EV_P_ ev_timer *w, int revents);
static void
add_request_cb(EV_P_ ev_timer *w, int revents);
static double
gen_t_req();
static void 
set_faulty_servers();
static void 
set_failing_point();
static void
remove_self();
static void 
benchmarking();
static void
print_round_data();
#endif


#endif

/* ================================================================== */
/* Global functions */
#if 1

void handle_next_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    uint32_t len, idx;
    srv_t *srv = NULL;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        terminate(1);
    }
    next_srv_t *next_srv = (next_srv_t*)ep->data;
    if (!next_srv) {
        error("next_srv is NULL\n");
        terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        terminate(1);
    }
    
    while (recv_len != 0) {
        if ((recv_len >= sizeof(uint64_t)) && !next_srv->byte_count) {
            next_srv->round_sqn = *(uint64_t*)recv_buf;
            recv_buf += sizeof(uint64_t);
            recv_len -= sizeof(uint64_t);
        }
        else {
            len = sizeof(uint32_t) - next_srv->byte_count;
            if (recv_len < len) {
                /* partially */
                memcpy(next_srv->buf, recv_buf, recv_len);
                next_srv->buf += recv_len;
                next_srv->byte_count += recv_len;
                return;
            }
            /* complete */
            memcpy(next_srv->buf, recv_buf, len);
            recv_buf += len;
            recv_len -= len;
            next_srv->round_sqn = next_srv->sqn;
       }
       next_srv->buf = (uint8_t*)&next_srv->sqn;
       next_srv->byte_count = 0;
       continue;
   }
#ifdef MSG_FLOW    
   info_wtime("[p%"PRIu32"] round_sqn=%"PRIu64"\n", next_srv->sid, next_srv->round_sqn);
#endif   
}

void handle_prev_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    HRT_TIMESTAMP_T t;
#ifdef MSG_DELAY    
    uint64_t rmt_ticks, lcl_ticks;
    double rmt_usecs, lcl_usecs;
#endif    
    int direct_cp;
    uint32_t len, idx;
    message_queue_t *q;
    srv_t *srv = NULL;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        terminate(1);
    }
    prev_srv_t *prev_srv = (prev_srv_t*)ep->data;
    if (!prev_srv) {
        error("prev_srv is NULL\n");
        terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        terminate(1);
    }
    
#if 1    
    if (prev_srv->sid != UINT32_MAX) {
        pthread_mutex_lock(&data.fd.prev_mutex);
        data.vertex_to_srv_map[prev_srv->sid].received_data = 1;
        pthread_mutex_unlock(&data.fd.prev_mutex);
    }
#endif    

#ifdef BENCHMARK
#ifndef BW_BENCH    
    uint64_t ticks;    
    if (ww_flag == WW_WAIT) {
        HRT_GET_TIMESTAMP(tww[!ww_flag]);
        HRT_GET_ELAPSED_TICKS(tww[ww_flag], tww[!ww_flag], &ticks);
        ww_usecs[ww_flag] += HRT_GET_USEC(ticks);        
        //info("\n# waiting += %lf usecs (poll_count=%"PRIu64")\n", HRT_GET_USEC(ticks), poll_count);
        poll_count = 0;
        ww_flag = !ww_flag;
    }
#endif    
    recv_bytes += recv_len;
#endif    

#ifdef BW_BENCH
    if (bw_bench_done) return;
    if (started_timer == 0) {
        HRT_GET_TIMESTAMP(t_round_start);
        started_timer = 1;
    }
    HRT_GET_TIMESTAMP(t);
    HRT_GET_ELAPSED_TICKS(t_round_start, t, &ticks);
    double usecs = HRT_GET_USEC(ticks);
    //info("[%lf] -- recv %d bytes\n", usecs, recv_len);
    if (usecs >= 5*1e7) {
        info("recv %"PRIu64" bytes; throughput: %lf Gbps\n", recv_bytes, .001*recv_bytes*8/usecs);
            bw_bench_done = 1;
            ev_set_cb(&w_throughput, terminate_cb);
            w_throughput.repeat = 0.5;
            ev_timer_again(data.loop, &w_throughput);
    }
    return;
#endif     
    //info_wtime("recv %d bytes from p%d\n", recv_len, prev_srv->sid);

    while (recv_len != 0) {
        direct_cp = 0;
        if (READ_HELLO == prev_srv->state) {
            if ((recv_len >= sizeof(uint32_t)) && !prev_srv->byte_count) 
            {
                prev_srv->sid = *(uint32_t*)recv_buf;
                recv_buf += sizeof(uint32_t);
                recv_len -= sizeof(uint32_t);
            }
            else {
                len = sizeof(uint32_t) - prev_srv->byte_count;
                if (recv_len < len) {
                    /* partially */
                    memcpy(prev_srv->buf, recv_buf, recv_len);
                    prev_srv->buf += recv_len;
                    prev_srv->byte_count += recv_len;
                    goto exit_work;
                    //return;
                }
                /* complete */
                memcpy(prev_srv->buf, recv_buf, len);
                recv_buf += len;
                recv_len -= len;
            }
            prev_srv->state = READ_UDINFO_LEN;
            prev_srv->buf = (uint8_t*)&prev_srv->ud_info.len;
            prev_srv->byte_count = 0;
#ifdef MSG_FLOW    
info_wtime("[p%"PRIu32"] Hello!\n", prev_srv->sid);
#endif
info_wtime("p%"PRIu32" -> Hello!\n", prev_srv->sid);
            continue;
        }
        else if (READ_UDINFO_LEN == prev_srv->state) {
            if ((recv_len >= sizeof(uint32_t)) && !prev_srv->byte_count) 
            {
                prev_srv->ud_info.len = *(uint32_t*)recv_buf;
                recv_buf += sizeof(uint32_t);
                recv_len -= sizeof(uint32_t);
            }
            else {
                len = sizeof(uint32_t) - prev_srv->byte_count;
                if (recv_len < len) {
                    /* partially */
                    memcpy(prev_srv->buf, recv_buf, recv_len);
                    prev_srv->buf += recv_len;
                    prev_srv->byte_count += recv_len;
                    goto exit_work;
                    //return;
                }
                /* complete */
                memcpy(prev_srv->buf, recv_buf, len);
                recv_buf += len;
                recv_len -= len;
            }
            prev_srv->ud_info.endpoint = malloc(prev_srv->ud_info.len);
            if (!prev_srv->ud_info.endpoint) {
                error("malloc\n");
                terminate(1);
            }
            prev_srv->state = READ_UDINFO;
            prev_srv->buf = (uint8_t*)prev_srv->ud_info.endpoint;
            prev_srv->byte_count = 0;   
            continue;
        }
        else if (READ_UDINFO == prev_srv->state) {
            len = prev_srv->ud_info.len - prev_srv->byte_count;
            if (recv_len < len) {
                /* partially */
                memcpy(prev_srv->buf, recv_buf, recv_len);
                prev_srv->buf += recv_len;
                prev_srv->byte_count += recv_len;
                goto exit_work;
                //return;
            }
            /* complete */
            memcpy(prev_srv->buf, recv_buf, len);
            recv_buf += len;
            recv_len -= len;
            
            /* Start monitoring predecessor */
            pthread_mutex_lock(&data.fd.prev_mutex);
            fd_ep_t* ep = fd_add_endpoint(&data.fd.prev_srv, 
                                        prev_srv->ud_info.endpoint);
            if (!ep) {
                pthread_mutex_unlock(&data.fd.prev_mutex);
                fd_error("fd_add_endpoint\n");
                terminate(1);
            }
            ep->sqn = data.vertex_to_srv_map[prev_srv->sid].sqn;
            ep->sid = prev_srv->sid;
#ifdef FD_INFO            
fd_info_wtime("New predecessor\n");
fd_print_endpoints(data.fd.prev_srv);
char epstr[EPSTR_LEN];
fd_info("   # start monitoring p%"PRIu32": %s\n\n", prev_srv->sid,
                ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, prev_srv->ud_info.endpoint));
#endif
            pthread_mutex_unlock(&data.fd.prev_mutex);            
            
            prev_srv->state = READ_MSG;
            prev_srv->buf = (uint8_t*)&prev_srv->msg;
            prev_srv->byte_count = 0;
            continue;
        }
        else if (READ_MTU == prev_srv->state) {
            len = MTU_MSG_SIZE - prev_srv->byte_count;
            if (recv_len < len) {
                /* partially */
                prev_srv->byte_count += recv_len;
                goto exit_work;
            }
            /* complete */
            recv_buf += len;
            recv_len -= len;
info_wtime("received MTU message from p%"PRIu32"\n", prev_srv->sid);            
            goto drop_message;
        }
        else if (READ_MSG == prev_srv->state) {
            len = sizeof(message_t) - prev_srv->byte_count;
            if (recv_len < len) {
                /* partially */
                memcpy(prev_srv->buf, recv_buf, recv_len);
                prev_srv->buf += recv_len;
                prev_srv->byte_count += recv_len;
                goto exit_work;
                //return;
            }
            /* complete */
            memcpy(prev_srv->buf, recv_buf, len);
            recv_buf += len;
            recv_len -= len;
            //info_wtime("[p%"PRIu32"] Received message\n", prev_srv->sid);
        }
        else if (READ_IN == prev_srv->state) {
            goto copy_input;
        }
        else {
            error("unknown state\n");
            terminate(1);
        }
        
        if (MSG_MTU == prev_srv->msg.type) {
            /* MTU message */
            prev_srv->state = READ_MTU;
            prev_srv->byte_count = sizeof(message_t);
            continue;
        }
        
#ifdef BENCHMARK
//if (MSG_INPUT == prev_srv->msg.type)
//    info_wtime("\n>>>  p%"PRIu32" (m%"PRIu32")-> (sqn=%"PRIu64")\n", 
//                    prev_srv->sid, prev_srv->msg.owner, prev_srv->msg.sqn);

#ifdef MSG_FLOW    
//info_wtime("[p%"PRIu32"] Completely received %s message: owner=%"PRIu32
//            "; inlen_fail=%"PRIu32"; sqn=%"PRIu64"; (work=%9.3lf)\n", prev_srv->sid,
//            (MSG_INPUT == prev_srv->msg.type ? "an INPUT" : 
//                (MSG_FAIL == prev_srv->msg.type ? "a FAIL" : "an UNKNOWN")),
//            prev_srv->msg.owner, prev_srv->msg.inlen_fail, prev_srv->msg.sqn, ww_usecs[WW_WORK]);

//dump_bytes(&prev_srv->msg, sizeof(message_t), "MESSAGE");
#endif 

        prev_srv->round_sqn = prev_srv->msg.sqn;

// The following code allows to measure the relative dalay of messages        
#ifdef MSG_DELAY   
        HRT_GET_TIMESTAMP(t);
        if (consensus_sqn > 2) {
            /* Collect delay data */
            HRT_GET_ELAPSED_TICKS(prev_srv->t_send, prev_srv->msg.t, &rmt_ticks);
            HRT_GET_ELAPSED_TICKS(prev_srv->t_recv, t, &lcl_ticks);
            rmt_usecs = HRT_GET_USEC(rmt_ticks);
            lcl_usecs = HRT_GET_USEC(lcl_ticks);
            if (bench_data.delay_tail->idx == BENCH_BUF_LEN) {
                /* Buffer full; allocate a new one */
                bench_buf_double_t *tail = bench_data.delay_tail;
                bench_data.delay_tail = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
                if (!bench_data.delay_tail) {
                    error("malloc (%s)\n", strerror(errno));
                    terminate(1);
                }
                memset(bench_data.delay_tail, 0, sizeof(bench_buf_double_t));
                tail->next = bench_data.delay_tail;
            }
            bench_data.delay_tail->buf[bench_data.delay_tail->idx] = lcl_usecs-rmt_usecs;
            bench_data.delay_tail->idx++;

            //info("delayed message m%"PRIu32" from p%"PRIu32" -- rmt=%9.3lf vs. lcl=%9.3lf\n", prev_srv->msg.owner, prev_srv->sid, rmt_usecs, lcl_usecs);
    if (lcl_usecs > 500+rmt_usecs && prev_srv->sid != prev_srv->msg.owner) {
        info("Warning: delayed message m%"PRIu32" from p%"PRIu32" -- rmt=%9.3lf vs. lcl=%9.3lf\n", prev_srv->msg.owner, prev_srv->sid, rmt_usecs, lcl_usecs);
    }
        }
        prev_srv->t_send = prev_srv->msg.t;
        prev_srv->t_recv = t;
#endif   

        msg_received++;
#endif        
    
        /* Completely received the message */
        if (MSG_FAIL == prev_srv->msg.type) {
            /* Failure notification */
            if (prev_srv->msg.sqn < consensus_sqn) {
                /* Outdated failure notification -- drop */
                goto drop_message;
            }
            else if (prev_srv->msg.sqn > consensus_sqn) {
                /* Premature failure notification */
                q = add_message(&premature_msgs, &prev_srv->msg, prev_srv->sid);
                if (NULL == q) {
                    error("add_message\n");
                    terminate(1);
                }
                goto drop_message;
            }
            else goto got_message;
        }
        else if (MSG_INPUT == prev_srv->msg.type) {
            /* Message owner */
            srv = &data.vertex_to_srv_map[prev_srv->msg.owner];
            /* By default we keep the input */
            prev_srv->state = READ_IN;
            if (prev_srv->msg.sqn > consensus_sqn) {
                /* Premature INPUT message */
//info("   [p%"PRIu32"] Premature INPUT\n", prev_srv->sid);
                q = add_message(&premature_msgs, &prev_srv->msg, prev_srv->sid);
                if (NULL == q) {
                    error("add_message\n");
                    terminate(1);
                }
                if (0 == prev_srv->msg.inlen_fail) {
                    /* Empty INPUT -- no need to read anything */
                    q->completed = 1;
                    goto drop_message;
                }
                else {
                    /* Store the INPUT for later */
//info("   [p%"PRIu32"] Store INPUT for later\n", prev_srv->sid);
                    prev_srv->buf = (uint8_t*)q->msg.input;
                    prev_srv->byte_count = 0;
                    prev_srv->q = q;
                    goto copy_input;
                }
            }
            if (0 == prev_srv->msg.inlen_fail) {
                /* Empty input */
//info_wtime("   [p%"PRIu32"] Empty INPUT\n", prev_srv->sid);
                goto got_input;
            }
            /* Non-empty input... */
            if (prev_srv->msg.inlen_fail <= recv_len) {
                /* ...no need to copy it */
//info_wtime("   [p%"PRIu32"] direct copy\n", prev_srv->sid);
                direct_cp = 1;
                goto got_input;
            }
            if (prev_srv->msg.sqn < consensus_sqn) {
                /* Outdated INPUT -- it will be dropped */
                prev_srv->buf = NULL;
                prev_srv->byte_count = 0;
                goto copy_input;
            }
            if (SRV_GOT_MSG & srv->state) {
                /* Already received INPUT -- it will be dropped */
            //idx = prev_srv->msg.owner * (data.G[data.activeG]->degree+1);
            //if (0 != data.sent_msgs[idx]) {
                /* Already received INPUT -- it will be dropped */
                prev_srv->buf = NULL;
                prev_srv->byte_count = 0;
                goto copy_input;
            }
            /* ...store INPUT temporarily in msg.input */
            if (prev_srv->inlen != prev_srv->msg.inlen_fail) 
            {
                /* Reallocate input */
                prev_srv->input = realloc(prev_srv->input, 
                                        prev_srv->msg.inlen_fail);
                if (NULL == prev_srv->input) {
                    error("realloc\n");
                    terminate(1);
                }
                prev_srv->inlen = prev_srv->msg.inlen_fail;
            }
            prev_srv->buf = prev_srv->input;
            prev_srv->byte_count = 0;
            goto copy_input;
        }
        else {
            error("[p%"PRIu32"] unknown message type\n", prev_srv->sid);
            terminate(1);
        }
        
copy_input:
        len = prev_srv->msg.inlen_fail - prev_srv->byte_count;
//info_wtime("   [p%"PRIu32"] copy input -- %"PRIu32" bytes needed; %"PRIu32" bytes available\n", prev_srv->sid, len, recv_len);
        if (recv_len < len) {
            /* partially */
            if (prev_srv->buf) {
                memcpy(prev_srv->buf, recv_buf, recv_len);
                prev_srv->buf += recv_len;
            }
            prev_srv->byte_count += recv_len;
            goto exit_work;
            //return;
        }
        /* complete */
        if (prev_srv->buf) {
            memcpy(prev_srv->buf, recv_buf, len);
//info("   got entire message\n");
        }
        recv_buf += len;
        recv_len -= len;
        if (prev_srv->q) {
            prev_srv->q->completed = 1;
        }

got_input:
        /* Got entire INPUT -- check if we should handle it... */
        if (prev_srv->msg.sqn != consensus_sqn) {
            /* Message not for this consensus round */
//info_wtime("   [p%"PRIu32"] Wrong round INPUT [%"PRIu64"] -- drop\n", prev_srv->sid, prev_srv->msg.sqn);
            if (direct_cp) {
                /* Skip input data */
                recv_buf += prev_srv->msg.inlen_fail;
                recv_len -= prev_srv->msg.inlen_fail;
            }
            goto drop_message;
        }
        srv = &data.vertex_to_srv_map[prev_srv->msg.owner];
        if (SRV_GOT_MSG & srv->state) {
            /* Already received INPUT -- drop */
        //idx = prev_srv->msg.owner * (data.G[data.activeG]->degree+1);
        //if (0 != data.sent_msgs[idx]) {
//info_wtime("   [p%"PRIu32"] Already received INPUT -- drop\n", prev_srv->sid);
            if (direct_cp) {
                /* Skip input data */
                recv_buf += prev_srv->msg.inlen_fail;
                recv_len -= prev_srv->msg.inlen_fail;
            }
            goto drop_message;
        }

        /* ...and store it */
        if (!(SRV_INPUT & srv->state) && (0 != prev_srv->msg.inlen_fail)) 
        {
            /* Store the input */
//info_wtime("   [p%"PRIu32"] store input\n", prev_srv->sid);
            if (prev_srv->msg.inlen_fail != srv->inlen) 
            {
                /* Reallocate space for input */
                srv->input = realloc(srv->input, prev_srv->msg.inlen_fail);
                if (NULL == srv->input) {
                    error("realloc\n");
                    terminate(1);
                }
                srv->inlen = prev_srv->msg.inlen_fail;
            }
            if (prev_srv->q) {
                /* Premature message -- by the time the input was received, 
                   the message is no longer outdated;
                   Note: no need to remove it from the queue of premature 
                   messages; it will be removed in the next round */
                memcpy(srv->input, prev_srv->q->msg.input, prev_srv->msg.inlen_fail);
            }
            else if (direct_cp) {
//info_wtime("   [p%"PRIu32"] direct copy\n", prev_srv->sid);
                memcpy(srv->input, recv_buf, prev_srv->msg.inlen_fail);
                recv_buf += prev_srv->msg.inlen_fail;
                recv_len -= prev_srv->msg.inlen_fail;
            }
            else {
                memcpy(srv->input, prev_srv->input, prev_srv->msg.inlen_fail);
            }
            set(&srv->state, SRV_INPUT);
        }
        
got_message:
//info_wtime("   [p%"PRIu32"] handle message\n", prev_srv->sid);
        handle_message(&prev_srv->msg, prev_srv->sid);
        
drop_message:
        /* Prepare for next message */
        if (prev_srv->q) {
            prev_srv->q = NULL;
        }
        prev_srv->state = READ_MSG;
        prev_srv->buf = (uint8_t*)&prev_srv->msg;
        prev_srv->byte_count = 0;  
        continue;        
    }
exit_work:
#ifdef BENCHMARK
    if (ww_flag == WW_WORK) {
        HRT_GET_TIMESTAMP(tww[!ww_flag]);
        HRT_GET_ELAPSED_TICKS(tww[ww_flag], tww[!ww_flag], &ticks);
        ww_usecs[ww_flag] += HRT_GET_USEC(ticks);
        //info("# working += %lf usecs\n", HRT_GET_USEC(ticks));
        ww_flag = !ww_flag;
    }
#endif
    return;
}

void* new_predecessor(void *conn)
{
    info_wtime("New predecessor connected\n");
    
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = (ep_t*)malloc(sizeof(ep_t));
    if (NULL == ep) {
        error("malloc (%s)\n", strerror(errno));
        return NULL;
    }
    memset(ep, 0, sizeof(ep_t));
    
    ep->connected = 1;
    ep->conn = conn;
    conn_ctx->ep = ep;
    conn_ctx->buffering = 1;
    
    ep->data = malloc(sizeof(prev_srv_t));
    if (NULL == ep->data) {
        error("malloc (%s)\n", strerror(errno));
        free(ep);
        return NULL;
    }
    prev_srv_t *prev_srv = (prev_srv_t*)ep->data;
    memset(prev_srv, 0, sizeof(prev_srv_t));
    prev_srv->state = READ_HELLO;
    prev_srv->buf = (uint8_t*)&prev_srv->sid;
    prev_srv->byte_count = 0;
    prev_srv->sid = UINT32_MAX;

    ep->head = &data.prev_srv_list;
    ac_ep_add(ep);    
    return ep;
}

void* new_successor(void *conn)
{
    int rv;
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = conn_ctx->ep;
    next_srv_t *next_srv = (next_srv_t*)ep->data;
    
    if (server_is_failed(next_srv->sid)) {
        /* Server failed in a previous round */
        return NULL;
    }
    if (server_failed_crt_round(next_srv->sid)) {
        /* Received failure notification in this round */
        return NULL;
    }

    info_wtime("Connected to p%"PRIu32" %s:%s\n", 
                next_srv->sid, ep->cd.ei.host, ep->cd.ei.port);
                
    conn_ctx->buffering = 1;
    next_srv->buf = (uint8_t*)&next_srv->sqn;
    next_srv->byte_count = 0;
        
    /* Send hello message; use a shared buffer ... */
    // TODO: send together with pending messages
    uint32_t bytes = sizeof(shared_buf_t) + sizeof(data.self) + 
            sizeof(data.fd.ud.ud_info.len) + data.fd.ud.ud_info.len;
    shared_buf_t *sh_buf = (shared_buf_t*)malloc(bytes);
    if (NULL == sh_buf) {
        error("malloc (%s)\n", strerror(errno));
        return NULL;
    }
    memset(sh_buf, 0, bytes);
    sh_buf->len = bytes - sizeof(shared_buf_t);
    *((uint32_t*)sh_buf->buf) = data.self;
    /* Also add UD info */
    *((uint32_t*)(sh_buf->buf+sizeof(uint32_t))) = data.fd.ud.ud_info.len;
    memcpy(sh_buf->buf+sizeof(uint64_t), data.fd.ud.ud_info.endpoint,
            data.fd.ud.ud_info.len);
    
    /* Send the message (asynch) */
#ifdef MSG_FLOW
info("   [p%"PRIu32"] send hello message\n", next_srv->sid);
#endif
    rv = ac_net_mod->isend(ep, sh_buf);
    if (rv) {
        error("isend\n");
        return NULL;
    }
    if (!sh_buf->shared_count) {
        free(sh_buf);
        sh_buf = NULL;
    }
    
    /* Send all pending messages (in order) */
    if (0 != send_pending_messages(ep)) {
        error("send_pending_messages\n");
        return NULL;
    }
        
    /* Connected */
    successor_count++;
    ep->connected = 1;
//info("   [p%"PRIu32"] connection established\n", next_srv->sid);
    
        
#ifdef BENCHMARK     
    if (successor_count == data.G[data.activeG]->degree) {
        if (AC_BENCH_THRP != bench_type) {
            if ((AC_BENCH_LAT != bench_type) || (data.self == 0)) {
                /* Schedule the add_request callback */
                //info("Connected to all successors -- schedule the add_request callback\n");
                w_add_request.repeat = NOW;
                ev_timer_again(data.loop, &w_add_request);
            }
        }
#if 1        
        else {
            /* Fill in the request poll */
            int i;
            for (i = 0; i < data.max_batching; i++) {
                rv = rp_add_request(&data.request_pool, 
                        request, data.req_size, NULL, 0, NULL);
                if (RP_FULL == rv) {
                    error("Not enough space in the request pool\n");
                    terminate(1);
                }
            }
        }
#endif        
    }
#endif   
    
    return ep;
}

void check_termination()
{
    message_t msg;
    sid_queue_t *sq = NULL;
    srv_t *srv = NULL;
    ep_t *ep = NULL;
    int rv;
    uint32_t idx, i;
    uint32_t sid;
    uint32_t bytes;
    shared_buf_t *sh_buf = NULL;

#ifdef AVOID_REDUNDANT
    prev_srv_t *prev_srv;
#endif
    
    uint32_t dead_count = 0;
    digraph_t *G = data.G[data.activeG];

    if (handling_premature_msgs) {
        /* Check for termination after handling the premature messages */
        return;
    }
    
    /* Check whether there are too many failures */
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        if (server_is_failed(sid)) {
            dead_count++;
        }
        else if (SRV_MSG_LOST & srv->state) {
            dead_count++;
        }
    }
    if (dead_count >= G->degree) {
        info_wtime("Too many failures\n");
        terminate(1);
    }
#if 0
    static int recv_all_mes = 0;
#endif    
    /* Check whether is safe to terminate */
    for (sid = 0; sid < data.n; sid++) {
        if (sid == data.self) continue;
        srv = &data.vertex_to_srv_map[sid];
        if (SRV_GOT_MSG & srv->state) {
            /* Already have a message from this server */
            continue;
        }
        if (SRV_MSG_LOST & srv->state) {
            /* The message is lost */
            continue;
        }
        if (server_is_failed(sid)) {
            /* This server failed a while ago */
            continue;
        }
//info("   Server p%d: neither input nor failed -- state=%"PRIu32"\n", sid, srv->state);            
        return;
    }
    if (NULL != data.g_array) {
        return;
    }
#if 0
    if (!recv_all_mes) {
        info_wtime("Received all messages\n");
        recv_all_mes = 1;
    }
#endif     

#if 1
    /* Wait until all messages are sent */
    if (ac_net_mod->bytes_to_send > 0) {
        //info("   Still sending (%"PRIu64" bytes to send)\n", ac_net_mod->bytes_to_send);
        return;   
    }

    /* Wait until the send buffers are empty */
    if (ac_net_mod->ongoing_bytes) {
        ep = data.next_srv_list;
        while (NULL != ep) {
            int bytes_on_socket = ac_net_mod->ongoing_bytes(ep);
            if (bytes_on_socket) {
#if 0                
                if (strncmp(ac_net_mod->name, "TCP", 3) == 0 && 
                        bytes_on_socket <= MTU_MSG_SIZE) 
                {
                    if (ep->mtu_sent) {
                        /* Already sent MTU message */
                        ep = ep->next;
                        continue;
                    }
                    info_wtime("%d bytes to send to p%"PRIu32"\n", bytes_on_socket, ((next_srv_t*)ep->data)->sid);
                    /* Send MTU message -- avoids delay due to Nagle's algorithm */                        
                    bytes = sizeof(shared_buf_t) + MTU_MSG_SIZE;
                    sh_buf = (shared_buf_t*)malloc(bytes);
                    if (NULL == sh_buf) {
                        error("malloc (%s)\n", strerror(errno));
                        terminate(1);
                    }
                    memset(sh_buf, 0, bytes);
                    sh_buf->len = bytes - sizeof(shared_buf_t);
                    ((message_t*)sh_buf->buf)->type = MSG_MTU;
                    rv = ac_net_mod->isend(ep, sh_buf);
                    if (rv) {
                        error("isend\n");
                        terminate(1);
                    }
                    if (!sh_buf->shared_count) {
                        free(sh_buf);
                        sh_buf = NULL;
                    }
                    ep->mtu_sent = 1;         
                }
#endif                
                //info_wtime("still %d bytes to send to p%"PRIu32"\n", bytes_on_socket, ((next_srv_t*)ep->data)->sid);
                return;
            }
            ep = ep->next;
        }
    }
#if 0    
    /* Reset MTU flag */
    if (strcmp(ac_net_mod->name, "TCP") == 0) {
        ep = data.next_srv_list;
        while (NULL != ep) {
            ep->mtu_sent = 0;
            ep = ep->next;
        }
    }
#endif    
#endif
#if 0    
    recv_all_mes = 0;
    info_wtime("Sent all messages\n");
#endif    
#if 0    
    /* Check whether all messages are sent */
    ep = data.next_srv_list;
    while (NULL != ep) {
        conn_ctx_t *send_ctx = (conn_ctx_t*)ep->conn;
        next_srv_t *next_srv = (next_srv_t*)ep->data;
        if (send_ctx->send_buf) {
info("   Still sending to p%"PRIu32"\n", next_srv->sid);
            return;
        }
        ep = ep->next;
    }
#endif    
    
    /* !!!!!! Yey - atomic broadcast completed !!!!!!!! */
    
    /* Remove servers from which no message was received */
#ifdef BENCHMARK
    bench_data.srv_count = 1; // self
#endif
    int remove = 0;
    for (sid = 0; sid < data.n; sid++) {
        if (sid == data.self) {
            continue;
        }
        if (server_is_failed(sid)) {
            /* This server failed a while ago */
            continue;
        }
        srv = &data.vertex_to_srv_map[sid];
        if (SRV_GOT_MSG & srv->state) {
#ifdef BENCHMARK
            bench_data.srv_count++;
#endif             
            continue;
        }
        if (!remove) {
            remove = 1;
            info_wtime("Removing servers: ");
        }    
        remove_server(sid);
        info("p%"PRIu32" ", sid);        
    }
    if (remove) {
        info("\n");    
    }
    
#ifdef BENCHMARK
    /* Compute bytes agreed upon */
    bench_data.msg_count = 0;
    bench_data.byte_count = 0;
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        if (!(SRV_INPUT & srv->state)) continue;
        /* Received non-empty input from this server */
        bench_data.byte_count += srv->inlen;
        bench_data.msg_count++;
    }
    agreed_on_byte_count += bench_data.byte_count;
#endif
    
    /* Increment consensus SQN */
    consensus_sqn++;

#ifdef AVOID_REDUNDANT
    /* Notify predecessors */
    ep = data.prev_srv_list;
    while (NULL != ep) {
        prev_srv = (prev_srv_t*)ep->data;
        if (prev_srv->round_sqn >= consensus_sqn) {
            goto next_predecessor;
        }
        if (server_is_failed(prev_srv->sid) || 
            server_failed_crt_round(prev_srv->sid)) 
        {
            goto next_predecessor;
        }
        if (!ep->connected) { 
            goto next_predecessor;
        }
        if (NULL == sh_buf) {
            bytes = sizeof(shared_buf_t) + sizeof(uint64_t);
            sh_buf = (shared_buf_t*)malloc(bytes);
            if (NULL == sh_buf) {
                error("malloc (%s)\n", strerror(errno));
                terminate(1);
            }
            memset(sh_buf, 0, bytes);
            sh_buf->len = bytes - sizeof(shared_buf_t);
            *((uint64_t*)sh_buf->buf) = consensus_sqn;
        }
        rv = ac_net_mod->isend(ep, sh_buf);
        if (rv) {
            error("isend\n");
            terminate(1); 
        }
next_predecessor:
        ep = ep->next;
    }
    if (sh_buf) {
        if (0 == sh_buf->shared_count) {
            /* All sends finished */
            free(sh_buf);
            sh_buf = NULL;
        }
    }
#endif    
    
#ifdef BENCHMARK    
    benchmarking();
    
    /* Apply inputs and send replies if needed */     
#ifdef AC_KVS                        
    // apply_inputs_to_sm();
#endif 
     
    /* Check join requests */
    check_join_requests();
    
    /* Mark own requests as handled */
    rp_complete_requests(&data.request_pool, 
                        (AC_BENCH_THRP != bench_type));
#else
    /* Apply inputs and send replies if needed */     
#ifdef AC_KVS                        
    // apply_inputs_to_sm();
#endif
    
    /* Check join requests */
    check_join_requests();
    
    /* Mark own requests as handled */
    rp_complete_requests(&data.request_pool, 1);
#endif 

    /* Clear matrix of already sent messages */
    memset(data.sent_msgs, 0, (G->degree + 1)*data.n);
        
//info_wtime("Resending FAILs:\n");    
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        /* Reset DONE flag */     
        unset(&srv->state, SRV_GOT_MSG);
        /* Reset MSG_LOST flag */
        unset(&srv->state, SRV_MSG_LOST);
        /* Reset INPUT flag */
        unset(&srv->state, SRV_INPUT);
        /* No need to free inputs */
        
        /* Resend early failure notifications of not removed servers;
           for removed servers, srv->fn == NULL */
        if (srv->fn == NULL) continue;
        memset(&msg, 0, sizeof(message_t));
        msg.type = MSG_FAIL;
        msg.inlen_fail = sid;
        msg.sqn = consensus_sqn;
        sq = srv->fn;
        while (sq != NULL) {
            /* Send notification... */
            msg.owner = sq->sid;
info_wtime("resend F(%"PRIu32"->%"PRIu32")\n", msg.inlen_fail, msg.owner);
            idx = get_predecessor_idx(G, msg.owner, msg.inlen_fail) +
                    msg.owner*(G->degree+1) + 1;
            send_message_further(&msg, idx, data.self);
            /* Handle failure notification */
            handle_failure_notification(msg.inlen_fail, msg.owner);
            /* ...and remove it */
            sq = sq->next;
            //free(sq);  
        }
    }    
                           
    /* Check list of prematurely received messages */
    handling_premature_msgs = 1;
    rv = handle_premature_messages(&premature_msgs, consensus_sqn, 
                                    handle_message);
    if (0 != rv) {
        error("cannot handle prematurely received messages\n");
        terminate(1);
    }
    handling_premature_msgs = 0;

    check_termination();
}

void poll_fd()
{
    uint32_t sid = UINT32_MAX;
    fd_ep_t *ep, *next;
    srv_t *srv = NULL;
    int failure = 0;
    if (!data.fd.failure) return;
    
    pthread_mutex_lock(&data.fd.prev_mutex);
    data.fd.failure--;
    ep = data.fd.prev_srv;
    while (ep) {
        next = ep->next;
        if (FD_EP_FAILED == ep->state) {
            /* Failure */
            char epstr[EPSTR_LEN];
            fd_info_wtime("FAILURE: %s\n", 
                    ac_net_mod->ud_ep_to_str(epstr, EPSTR_LEN, ep->endpoint));
#if 0
            pthread_mutex_unlock(&data.fd.prev_mutex);
            terminate(1);
#endif
            if (ep->sid < data.n) {
                srv = &data.vertex_to_srv_map[ep->sid];
                if (srv->sqn == ep->sqn) {
                    sid = ep->sid;
                    failure = 1;
                    info_wtime("FAILURE: p%"PRIu32"\n", ep->sid);
                }
            }
            fd_rm_ep(&data.fd.prev_srv, ep);
            if (failure) {
                break;
            }
        }
        ep = next;
    }
    pthread_mutex_unlock(&data.fd.prev_mutex);
    if (failure) {
#ifdef BENCHMARK
        if (AC_BENCH_THRP != bench_type) {
            /* Ignore failures for the throughput benchmark */
            send_failure_notification(sid);
        }
#endif        
        pthread_mutex_lock(&data.fd.next_mutex);
        ep = data.fd.next_srv;
        while (ep) {
            next = ep->next;
            if ((ep->sid == sid) && (ep->sqn == srv->sqn)) {
                fd_rm_ep(&data.fd.next_srv, ep);
            }
            ep = next;
        }
        pthread_mutex_unlock(&data.fd.next_mutex);
    }
}

void poll_request_pool()
{
#ifdef BENCHMARK
    if (bench_done) return;
#endif
    
    /* Check whether to start a new consensus round */
    if (data.request_pool.empty) return;
    
    /* Eager policy for handling requests */
    digraph_t *G = data.G[data.activeG];
    uint32_t idx = data.self*(G->degree+1);
    srv_t *myself = &data.vertex_to_srv_map[data.self];
    
#ifdef BW_BENCH    
    if (bw_bench_done) {
        return;
    }
    else {
#else
    if (0 == data.sent_msgs[idx]) {
#endif        
        /* Pack requests together into an input... */
        set(&myself->state, SRV_INPUT);
#ifdef BENCHMARK        
        if (AC_BENCH_THRP == bench_type) {
            myself->inlen = rp_pack_requests(&data.request_pool, 
                &(myself->input), batching_factor * data.req_size);
        }
        else
#endif              
        myself->inlen = rp_pack_requests(&data.request_pool, 
                                            &(myself->input), 0);
                  


#ifdef BENCHMARK        
        /* Measure the time of an abcast round */
        if (timer) {
#ifdef BW_BENCH    
       if (!started_timer) {
#endif   
            HRT_GET_TIMESTAMP(t_round_start);
#ifdef BW_BENCH    
            started_timer = 1;
       }
       if (0 == warmup_done) {        
        HRT_TIMESTAMP_T t;
        uint64_t ticks;
        double usecs;
    HRT_GET_TIMESTAMP(t);
    HRT_GET_ELAPSED_TICKS(t_round_start, t, &ticks);
    usecs = HRT_GET_USEC(ticks);
    if (usecs >= 1e7) {
        info("   ### WARMUP DONE ###\nrecv %"PRIu64" bytes during warmup; throughput: %lf Gbps\n", recv_bytes, .001*recv_bytes*8/usecs);
        HRT_GET_TIMESTAMP(t_round_start);
        recv_bytes = 0;
        warmup_done = 1;
    }
       }
#endif   
        
        }
#endif        
    
        /* ...and send it to all successors */
        message_t msg;
        memset(&msg, 0, sizeof(message_t));
        msg.type = MSG_INPUT;                    
        msg.owner = data.self;
        msg.inlen_fail = myself->inlen;
        msg.sqn = consensus_sqn;
#ifdef MSG_FLOW    
info_wtime("Initiate new round -- own message [%"PRIu32" bytes]\n", msg.inlen_fail);
#endif
#ifdef BENCHMARK
        ww_usecs[0] = 0, ww_usecs[1]= 0, send_usecs = 0;
#ifndef BW_BENCH    
        recv_bytes = 0, sent_bytes = 0;
#endif         
        ww_flag = WW_INIT;
        HRT_GET_TIMESTAMP(tww[WW_WORK]);
#endif        

        send_message_further(&msg, idx, data.self); 
    }
}

int server_is_failed(uint32_t sid)
{
    return (SRV_FAILED & data.vertex_to_srv_map[sid].state);
}

int server_failed_crt_round(uint32_t sid) 
{
    return (NULL != data.vertex_to_srv_map[sid].fn);
}


#ifdef BENCHMARK 
void benchmark_init()
{    
    int rv, i;
    
    warmup = WARMUP_COUNT;

    if (data.t_round_stream) {
        bench_data.round_head = (bench_buf_round_t*)malloc(sizeof(bench_buf_round_t));
        if (!bench_data.round_head) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(bench_data.round_head, 0, sizeof(bench_buf_round_t));
        bench_data.round_tail = bench_data.round_head;
    }

#ifdef MSG_DELAY    
    bench_data.delay_head = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
    if (!bench_data.delay_head) {
        error("malloc (%s)\n", strerror(errno));
        terminate(1);
    }
    memset(bench_data.delay_head, 0, sizeof(bench_buf_double_t));
    bench_data.delay_tail = bench_data.delay_head;
#endif    
 
    if (data.throughput_stream) {
        bench_data.throughput_head = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
        if (!bench_data.throughput_head) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(bench_data.throughput_head, 0, sizeof(bench_buf_double_t));
        bench_data.throughput_tail = bench_data.throughput_head;
    }

    if (data.t_request_stream) {
        bench_data.request_head = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
        if (!bench_data.request_head) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(bench_data.request_head, 0, sizeof(bench_buf_double_t));
        bench_data.request_tail = bench_data.request_head;
    }
    
    if (data.t_round_stream) {
        /* Write header */
        fprintf(data.t_round_stream, 
            "         SQN    SRVS    BYTES    TIME(us)    WORK(us)    WAIT(us)   BW(Gbps)    RX_BW(Gbps)    TX_BW(Gbps)  OVERALL\n");
    }

    if (data.throughput_stream) {
        /* Initialize a watcher that measures throughput */
        ev_timer_init(&w_throughput, throughput_cb, 0., 0.);
        ev_set_priority(&w_throughput, EV_MAXPRI-1);
    }
    
    /* Initialize request */
    request = (kvs_ht_cmd_t*)malloc(data.req_size);
    memset(request, 'x', data.req_size);
    request->type = KVS_PUT;
    request->key_len = data.req_size - sizeof(kvs_ht_cmd_t);
    request->value_len = 0;
#if 0
    if (AC_BENCH_THRP == bench_type) {
        /* Fill in the request poll */
        for (i = 0; i < max_batching; i++) {
            rv = rp_add_request(&data.request_pool, 
                        request, data.req_size, NULL, 0, NULL);
            if (RP_FULL == rv) {
                error("Not enough space in the request pool\n");
                terminate(1);
            }
        }
    }
#endif    
    
    /* For failure scenarios */
    faulty_servers = (uint8_t*)malloc(sizeof(uint8_t)*data.n);
    fail_count = data.G[data.activeG]->degree - 1;
    
    /* Initialize a watcher that periodically generates requests */
    ev_timer_init(&w_add_request, add_request_cb, 0., 0.);
    ev_set_priority(&w_add_request, EV_MAXPRI-1);
}


void benchmark_destroy()
{
    uint32_t i;
    /* Print round data */
    if (data.t_round_stream && data.self == 0) {
        print_round_data();
        if (bench_data.round_head) {
            free(bench_data.round_head);
            bench_data.round_head = NULL;
        }
        fclose(data.t_round_stream);
        data.t_round_stream = NULL;
    }

#ifdef MSG_DELAY    
    /* Print delay data */
    if (data.delay_stream) {
        bench_buf_double_t *bench_buf;
        while (NULL != (bench_buf = bench_data.delay_head)) {
            bench_data.delay_head = bench_buf->next;
            for (i = 0; i < bench_buf->idx; i++) {
                fprintf(data.delay_stream, "%9.3lf ", bench_buf->buf[i]);
            }
            free(bench_buf);
        }
        fclose(data.delay_stream);
        data.delay_stream = NULL;
    }
#endif    
    
    /* Print throughput data */
    if (data.throughput_stream && data.self == 0) {
        bench_buf_double_t *bench_buf;
        while (NULL != (bench_buf = bench_data.throughput_head)) {
            bench_data.throughput_head = bench_buf->next;
            for (i = 0; i < bench_buf->idx; i++) {
                fprintf(data.throughput_stream, "%9.3lf ", bench_buf->buf[i]);
            }
            free(bench_buf);
        }
        fclose(data.throughput_stream);
        data.throughput_stream = NULL;
    }

    /* Print request data */
    if (data.t_request_stream && data.self == 0) {
        bench_buf_double_t *bench_buf;
        while (NULL != (bench_buf = bench_data.request_head)) {
            bench_data.request_head = bench_buf->next;
            for (i = 0; i < bench_buf->idx; i++) {
                fprintf(data.t_request_stream, "%9.3lf ", bench_buf->buf[i]);
            }
            free(bench_buf);
        }
        fclose(data.t_request_stream);
        data.t_request_stream = NULL;
    }

    if (data.t_round_stream) {
        fclose(data.t_round_stream);
        data.t_round_stream = NULL;
    }
    
    ev_timer_stop(data.loop, &w_throughput);
    ev_timer_stop(data.loop, &w_add_request);
    if (faulty_servers) {
        free(faulty_servers);
        faulty_servers = NULL;
    }
    if (request) {
        free(request);
        request = NULL;
    }
}
#endif

#endif

/* ================================================================== */
/* Local functions */
#if 1

/**
 * Handle message receive from predecessor
 */
static void
handle_message(message_t *msg, uint32_t from_sid) 
{
    digraph_t *G = data.G[data.activeG];
    uint32_t idx, i;

#ifdef MSG_FLOW    
    if (MSG_INPUT == msg->type) {
        info_wtime("RECEIVED <INPUT, p%"PRIu32", %"PRIu32
            " bytes> [sqn=%"PRIu64"] (from p%"PRIu32")\n", 
            msg->owner, msg->inlen_fail, msg->sqn, from_sid);
    }
    else if (MSG_FAIL == msg->type) {
        info_wtime("RECEIVED <FAIL, p%"PRIu32", p%"PRIu32
            "> [sqn=%"PRIu64"] (from p%"PRIu32")\n", 
            msg->inlen_fail, msg->owner, msg->sqn, from_sid);
    }
#endif    
    
    /* Disseminate message further (if needed) */
    idx = msg->owner * (G->degree+1);                  /* <INPUT, pk> */
    if (MSG_FAIL == msg->type) {                    /* <FAIL, pj, pk> */
        /* Find index of predecessor from the P.O.W. of pk */
        i = get_predecessor_idx(G, msg->owner, msg->inlen_fail);
        if (UINT32_MAX == i) {
            /* Digraph inconsistency: this should never happen */
            error("digraph inconsistency\n");
            terminate(1);
        }
        idx += i + 1;
    }
    if (0 != data.sent_msgs[idx]) return;
    
    send_message_further(msg, idx, from_sid);

    if (msg->sqn != consensus_sqn) {
        return;
    }
    
    if (MSG_FAIL == msg->type) {     /* received <FAIL, p_j, p_k> */
        /* Handle notification, from server msg->owner, of 
           server msg->inlen_fail's failure */
        handle_failure_notification(msg->inlen_fail, msg->owner);
    }
    else {                                   /* received <INPUT, x_j> */
        /* Handle server msg->owner's input (msg->inlen_fail bytes) */
        handle_input(msg->owner, msg->inlen_fail, from_sid);
    }
}

static void 
handle_failure_notification(uint32_t pj, uint32_t pk)
{
    sid_queue_t *sq = NULL;
    g_array_t *ga = NULL;
    tuple_t *in = NULL, *out = NULL;
    digraph_t *G = NULL;
    g_server_t *g_srv = NULL, *g_srv_ps = NULL;
    srv_t *srv = NULL;
    uint32_t i;
    uint32_t sid;
    int no_termination = 0;
  
    //~ info("   Server p%"PRIu32" knows of server p%"PRIu32"'s failure\n", 
                    //~ pk, pj);

    if (server_is_failed(pj)) {
        /* Server failed in a previous round -- ignore */
        return;
    }

    srv = &data.vertex_to_srv_map[pj];

    /* Add g[xj] only if there is no mj */
    if (!(SRV_GOT_MSG & srv->state)) {
        /* Add g[xj] to the array of digraphs g */
        ga = g_array_entry_add(&data.g_array, pj);
        if (NULL == ga) {
            error("cannot create g[x%"PRIu32"]\n", pj);
            terminate(1);
        }
    }
    
    /* Add failure notification to the list */
    sq = srv->fn;
    while (sq != NULL) {
        if (sq->sid == pk) {
            /* <FAIL, pj, pk> is already in the list;
               because of the resends */
            no_termination = 1;
            goto already_have_it;
        }
        sq = sq->next;
    } /* sq == NULL */
    /* Add <FAIL, pj, pk> to the list of failure notifications */
    sq = (sid_queue_t*)malloc(sizeof(sid_queue_t));
    if (NULL == sq) {
        error("malloc (%s)\n", strerror(errno));
        terminate(1);
    }
    sq->sid = pk;
    sq->next = srv->fn;
    srv->fn = sq;


already_have_it:
    
print_failure_notifications(pj);
g_array_print(data.g_array);
 
    G = data.G[data.activeG];
    ga = data.g_array;
    /* Foreach g[x] that contains pj */
    while (ga != NULL) {                              /* Digraph g[x] */
//info("Dealing with digraph g[x%"PRIu32"]\n", ga->ge.self);
        g_srv = g_server_search(&ga->ge, pj);
        if (NULL == g_srv) {
            /* Digraph g[x] does not contain pj */
            ga = ga->next;
            continue;
        }
        /* This g[x] contains pj */
//info("Digraph g[x%"PRIu32"] contains server p%"PRIu32"\n", ga->ge.self, g_srv->sid);        
        if (g_server_has_successors(&ga->ge, g_srv)) {
            /* Check whether pk is one of them */
            if (g_server_is_successor_of(&ga->ge, pk, g_srv)) {
                /* Remove (pj,pk) edge */
                g_successor_rm(&ga->ge, g_srv, pk);
            }
        }
        else {                       /* pj has not successors in g[x] */
//info("Server p%"PRIu32" has no successors in digraph g[x%"PRIu32"]\n", g_srv->sid, ga->ge.self);
            /* Create FIFO queue with pj's successors (except pk) */
            in = tuple_queue; out = tuple_queue;
            for (i = 0; i < G->degree; i++) {
                sid = get_successor(G, pj, i);
                if (sid == pk) continue;
                /* Actually is important to add yourself: if you don't, 
                 * you don't need to wait for your failure notification, 
                 * but other do -- so, you'll finish without sending 
                 * FAIL(pj, self) */
                //~ if (sid == data.self) continue;
                if (server_is_failed(sid)) {
                    /* This successor failed in a previous round */
                    continue;
                }
                /* Add tuple (pj, sid) to the queue */
//info(">> Add tuple (p%"PRIu32", p%"PRIu32") to FIFO queue\n", pj, sid);
                in->pp = pj;
                in->ps = sid;
                in++;
            }
            
            while (out < in) {    /* Extract tuple (out->pp, out->ps) */
//info("Extract tuple (p%"PRIu32", p%"PRIu32") from FIFO queue\n", out->pp, out->ps);                
                /* Check whether out->ps is already in g[x] */
                g_srv_ps = g_server_search(&ga->ge, out->ps);
                if (g_srv_ps != NULL) {
                    /* out->ps already in; just add an edge (out->pp, out->ps) to g[x] */
                    if (0 != g_successor_add(&ga->ge, out->pp, g_srv_ps)) {
                        error("cannot add edge (p%"PRIu32", p%"PRIu32
                                ") to g[x%"PRIu32"]\n", out->pp, out->ps, 
                                ga->ge.self);
                        terminate(1);
                    }
                    
                    /* Increment out index */
                    out++;
                    continue;
                }
                /* Augment the FIFO queue */
                if (server_failed_crt_round(out->ps)) {
                    /* Server out->ps failed in this rounds; 
                       maybe it sent x to its successors before failing 
                       -> add out->ps's non-faulty successors to g[x] */
                    for (i = 0; i < G->degree; i++) {
                        sid = get_successor(G, out->ps, i);
                        //~ if (sid == data.self) continue;
                        if (server_is_failed(sid)) {
                            /* This successor failed in a previous round */
                            continue;
                        }
                        sq = data.vertex_to_srv_map[out->ps].fn;
                        while (NULL != sq) {
                            if (sq->sid == sid) {
                                /* <FAIL, out->ps, sid> in the list */
                                break;
                            }
                            sq = sq->next;
                        }
                        if (NULL != sq) {
                            /* Do not add tuple (out->ps, sid) */
                            continue;
                        }
                        in->pp = out->ps;
                        in->ps = sid;
//info("++Add tuple (p%"PRIu32", p%"PRIu32") to FIFO queue\n", out->ps, sid);
                        in++;
                    }
                }
                /* Add edge (out->pp, out->ps) to g[x] */
                if (0 != g_successor_add(&ga->ge, out->pp,
                            g_server_insert(&ga->ge, out->ps)))
                {
                    error("cannot add edge (p%"PRIu32", p%"PRIu32
                            ") to g[x%"PRIu32"]\n", out->pp, out->ps, 
                            ga->ge.self);
                    terminate(1);
                }
                
                /* Increment out index */
                out++;
            }
        }
        
        /* Prune digraph g[x]: first, remove all servers 
           that cannot have received x... */
        while ((g_srv = g_server_no_path_search(&ga->ge)) != NULL) {
//info("Removing p%"PRIu32" from digraph g[x%"PRIu32
//        "] (no input)\n", g_srv->sid, ga->ge.self);            
            g_server_rm(&ga->ge, g_srv);            
        }

        /* ...then, if all the servers are failed, 
           destroy the digraph (breaks loops) */
        if (g_server_all_failed(&ga->ge, server_failed_crt_round)) {
            /* No need to wait for ga->ge.self's input anymore */
            set(&data.vertex_to_srv_map[ga->ge.self].state, SRV_MSG_LOST);
//info("Removing digraph g[x%"PRIu32"] (only failed servers)\n", ga->ge.self);            
            
            /* Remove the digraph from the array */
            sid = ga->ge.self;
            ga = ga->next;
            g_array_entry_rm(&data.g_array, sid);            

            continue;
        }
               
        ga = ga->next;    
    }

g_array_print(data.g_array);

    if (!no_termination) {
        check_termination();
    }
}

static void
handle_input(uint32_t pj, uint32_t inlen, uint32_t from_sid)
{
    uint32_t idx, len = 0;
    message_t msg;
    srv_t *myself = NULL;
    digraph_t *G = data.G[data.activeG];
    
    //info("   Received server p%"PRIu32"'s input [%"PRIu32" bytes]\n", pj, inlen);
    
    /* Check whether already sent own input */
    idx = data.self*(G->degree+1);
    if (0 == data.sent_msgs[idx]) {
#ifdef BENCHMARK
        ww_usecs[0] = 0, ww_usecs[1]= 0, send_usecs = 0;
        recv_bytes = 0, sent_bytes = 0;
        ww_flag = WW_INIT;
        HRT_GET_TIMESTAMP(tww[WW_WORK]);
#endif

        /* Pack requests together into an input... */
        //info_wtime("Send own message\n");
        myself = &data.vertex_to_srv_map[data.self];
#ifdef BENCHMARK        
        if (AC_BENCH_THRP == bench_type)
            myself->inlen = rp_pack_requests(&data.request_pool, 
                    &myself->input, batching_factor * data.req_size);
        else
#endif        
            myself->inlen = rp_pack_requests(&data.request_pool, 
                            &myself->input, 0);
        if (0 != myself->inlen) {
            /* Non-empty input */
            set(&myself->state, SRV_INPUT);
        }

#ifdef BENCHMARK        
        /* Measure the time of an abcast round */
        if (timer) {
            HRT_GET_TIMESTAMP(t_round_start);
        }
#endif        
        
        /* ...and send it to all successors */
        memset(&msg, 0, sizeof(message_t));
        msg.type = MSG_INPUT;                    
        msg.owner = data.self;
        msg.inlen_fail = myself->inlen;
        msg.sqn = consensus_sqn;
        send_message_further(&msg, idx, data.self); 
    }
    
    /* No need to wait for pj's input anymore */
    set(&data.vertex_to_srv_map[pj].state, SRV_GOT_MSG);
#ifdef MSG_FLOW    
    info_wtime("Got m%"PRIu32"\n", pj);
#endif    
     
#ifdef BENCHMARK
//    info("     [x] m%"PRIu32"/p%"PRIu32" -- wait=%9.3lf us; work=%9.3lf us; bytes_to_send=%"PRIu64"; msg_received=%d\n", pj, from_sid, ww_usecs[WW_WAIT], ww_usecs[WW_WORK], ac_net_mod->bytes_to_send, msg_received);
    msg_received = 0;
#endif     
   
    /* Remove digraph g[xj] (if it exists) */
    g_array_entry_rm(&data.g_array, pj);

    check_termination();
}

static void 
send_message_further(message_t *msg, uint32_t send_idx, uint32_t from_sid) 
{
    int numbytes, rv;
    uint64_t len;
    uint32_t idx, i;
    uint32_t degree = data.G[data.activeG]->degree;
    uint8_t *buf;
    srv_t *srv = NULL;
    message_queue_t *q;
    ep_t *ep = NULL;
    next_srv_t *next_srv = NULL;
    shared_buf_t *sh_buf = NULL;

#ifdef BENCHMARK
    HRT_TIMESTAMP_T t1, t2;
    uint64_t ticks;

    HRT_GET_TIMESTAMP(t1);
#ifdef MSG_DELAY    
    HRT_GET_TIMESTAMP(msg->t);
#endif    
#endif    

#if 0
    TIMER_INIT;
    if (timer) {
        TIMER_START("Sending messages further (%"PRIu32" bytes) ... ");
    }
#endif 

#ifdef MSG_FLOW    
    info_wtime("Sending message further (%zu bytes)\n", 
        sizeof(message_t) + (MSG_INPUT == msg->type ? msg->inlen_fail: 0));
#endif
//info("Sending m%"PRIu32"\n", msg->owner);
    
    /* Send message to all successors */
    ep = data.next_srv_list;
    while (NULL != ep) {
        next_srv = (next_srv_t*)ep->data;
        srv = &data.vertex_to_srv_map[next_srv->sid];
        
        if (next_srv->sid == msg->owner) {
            /* Message owner - no need to resend message */
#ifdef MSG_FLOW
info("   [p%"PRIu32"] owner\n", next_srv->sid);
#endif
            goto next_successor;
        }
        if (next_srv->sid == from_sid) {
            /* Do not send back to predecessor */
#ifdef MSG_FLOW
info("   [p%"PRIu32"] sender\n", next_srv->sid);
#endif
            goto next_successor;
        }
#ifdef AVOID_REDUNDANT
        if (next_srv->round_sqn > msg->sqn) {
            /* Redundant message - no need to send */
#ifdef MSG_FLOW
info("   [p%"PRIu32"]'s sqn=%"PRIu64"\n", next_srv->sid, next_srv->round_sqn);
#endif
#ifdef BENCHMARK
            avoid_redundant_count++;
#endif            
            goto next_successor;
        }
#endif

        if (server_is_failed(next_srv->sid) || 
            server_failed_crt_round(next_srv->sid)) {
            /* Failed server - no need to send message */
#ifdef MSG_FLOW
info("   [p%"PRIu32"] failed\n", next_srv->sid);
#endif
            goto next_successor;
        }
        else {
            if ((MSG_FAIL == msg->type) && 
                    (msg->inlen_fail == next_srv->sid))
            {
                /* Do not send a server his own failure notification */
                goto next_successor;
            }
        }
        if (!ep->connected) { 
            /* We are not yet connected to this server; store message 
               for sending it after connection
               Note: no need to store the input since we have it */
#ifdef MSG_FLOW            
info("   [p%"PRIu32"] not connected\n", next_srv->sid);
#endif
            
            q = add_message(&next_srv->messages, msg, from_sid);
            if (NULL == q) {
                error("cannot add pending msg to the queue\n");
                terminate(1);
            }
//~ info_wtime("Adding message to queue %zd\n", msg->inlen_fail + sizeof(message_t));
            if ((MSG_INPUT == msg->type) && (0 != msg->inlen_fail)) {
//~ info("msg->type=%"PRIu8"; len=%"PRIu32"; q->msg.len=%"PRIu32"\n", msg->type, msg->inlen_fail, q->msg.inlen_fail);
                memcpy(q->msg.input, 
                       data.vertex_to_srv_map[msg->owner].input,
                       msg->inlen_fail);
            }
            goto next_successor;
        }

        /* Copy message into shared buffer */
        if (NULL == sh_buf) {
            len = sizeof(message_t);
            if (MSG_INPUT == msg->type) {
                len += msg->inlen_fail;
            }
            sh_buf = (shared_buf_t*)malloc(sizeof(shared_buf_t) + len);
            if (NULL == sh_buf) {
                error("malloc (%s)\n", strerror(errno));
                terminate(1);
            }
            /* No sharing ... yet */
            sh_buf->shared_count = 0;
            /* Length */
            sh_buf->len = len;
            /* Message */
            memcpy(sh_buf->buf, msg, sizeof(message_t));
            if (len > sizeof(message_t)) {
                /* and data */
                memcpy(sh_buf->buf + sizeof(message_t), 
                      data.vertex_to_srv_map[msg->owner].input,
                      msg->inlen_fail);
            }           
        }
#ifdef MSG_FLOW            
//info("[%p] -> ", ep->conn); dump_bytes(sh_buf->buf, sh_buf->len, "SENDING_DATA");
#endif
        
        /* Send the message (asynch) */
#ifdef MSG_FLOW            
info("   [p%"PRIu32"] sending\n", next_srv->sid);
#endif
//info("  (m%"PRIu32"/p%"PRIu32")-> p%"PRIu32" (sqn=%"PRIu64")\n", msg->owner, from_sid, next_srv->sid, msg->sqn);
        rv = ac_net_mod->isend(ep, sh_buf);
        if (rv) {
            error("isend\n");
            terminate(1); 
        }
#ifdef BENCHMARK
        sent_bytes += sh_buf->len;
#endif

#if 0
        pthread_mutex_lock(&data.fd.next_mutex);
        srv->sent_data = 1;
        pthread_mutex_unlock(&data.fd.next_mutex);
#endif            
next_successor:
        ep = ep->next;
    }
#if 0
    if (timer) {
        TIMER_STOP;
    }
#endif
    
    /* Mark message as sent */
    if (send_idx != UINT32_MAX) {
        data.sent_msgs[send_idx] = 1;
    }
cleanup:    
    if (sh_buf) {
        if (0 == sh_buf->shared_count) {
            /* All sends finished */
            free(sh_buf);
            sh_buf = NULL;
        }
    }

#ifdef BENCHMARK
    HRT_GET_TIMESTAMP(t2);
    HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
    send_usecs += HRT_GET_USEC(ticks);

    if (ww_flag == WW_INIT) {
        ww_flag = WW_WORK;
        HRT_GET_TIMESTAMP(tww[!ww_flag]);
        HRT_GET_ELAPSED_TICKS(tww[ww_flag], tww[!ww_flag], &ticks);
        ww_usecs[ww_flag] += HRT_GET_USEC(ticks);
#ifndef BW_BENCH        
        //info("# working = %lf usecs (init)\n", ww_usecs[ww_flag]);
#endif
        ww_flag = !ww_flag;
    }
#endif
}

static void 
send_failure_notification(uint32_t sid)
{
    message_t msg;
    int idx;
    digraph_t *G = data.G[data.activeG];
    
    info("Server p%"PRIu32" failed\n", sid);
    idx = get_predecessor_idx(G, data.self, sid);
            
    /* Check whether the notification was already sent */
    idx += data.self*(G->degree+1) + 1;
    if (1 == data.sent_msgs[idx])    /* notification already sent */
        return;
        
    /* Create message with failure notification */
    memset(&msg, 0, sizeof(message_t));
    msg.type = MSG_FAIL;                    
    msg.owner = data.self;
    msg.inlen_fail = sid;
    msg.sqn = consensus_sqn;
    send_message_further(&msg, idx, data.self);  
    
    /* Handle failure notification */
    handle_failure_notification(sid, data.self);
}

/* ================================================================== */

static void 
check_join_requests()
{
    int rv,
        just_check = 1;   /* Postpone the reply so that the CTRL SM is updated */
    uint32_t bytes, offset, sid, empty;
    kvs_ht_cmd_t *cmd = NULL;
    kvs_ht_reply_t *reply;
    shared_buf_t *sh_buf;
    srv_t *srv = NULL;
    digraph_t *G = data.G[data.activeG];
    
loop_through_inputs:
    empty = 0;
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        if (!(SRV_INPUT & srv->state)) continue;
        /* Received non-empty input from this server */
        offset = 0;
        while (offset < srv->inlen) {
            cmd = (kvs_ht_cmd_t*)((uint8_t*)srv->input + offset);
            if (CTRL_JOIN != cmd->type) {
                goto next_request;
            }
            for (; empty < data.n; empty++) {
                if (server_is_failed(empty)) break;
            }
            if (empty >= data.n) {
                /* No place for new server */
                if (just_check) {
                    info_wtime("No place for new servers\n");
                    if (sid == data.self) {
                        /* Command from own client -- send notification */
                        bytes = sizeof(shared_buf_t) + sizeof(kvs_ht_reply_t);
                        sh_buf = (shared_buf_t*)malloc(bytes);
                        if (NULL == sh_buf) {
                            error("malloc (%s)\n", strerror(errno));
                            terminate(1);
                        }
                        memset(sh_buf, 0, bytes);
                        sh_buf->len = bytes - sizeof(shared_buf_t);
                        reply = (kvs_ht_reply_t*)sh_buf->buf;
                        reply->type = REPLY_RC;
                        reply->rc = 1;
                        rv = reply_to_client(offset, sh_buf);
                        if (rv) {
                            error("reply_to_client\n");
                            terminate(1);
                        }
                    }
                }
                else return;
            }
            else {
                /* Add new server */
                srv_t *added_srv = &data.vertex_to_srv_map[empty];
                if (just_check) {
                    info_wtime("Adding server p%"PRIu32" (%s:%s) in round #%"PRIu64"\n", 
                                empty, ((net_id_t*)(cmd->data))->host, 
                                ((net_id_t*)(cmd->data))->ac_port, consensus_sqn);
                    
                    /* Directly update the data in the CTRL SM */
                    added_srv->srv_value->failed = 0;
                    memcpy(&added_srv->srv_value->ni,
                            cmd->data, sizeof(net_id_t));
                    empty++;
                }
                else {
                    unset(&added_srv->state, SRV_FAILED);
                    if (sid == data.self) {
                        /* Command from own client -- reply */
                        uint32_t ctrl_len = 
                                    get_kvs_ht_bytes(data.ctrl_sm);
                        uint32_t sm_len = 
#ifdef AC_KVS                        
                                    get_kvs_ht_bytes(data.kvs);
#else                    
                                    0;
#endif                                    
                        //info_wtime("Need to create snapshots: ctrl_len=%"PRIu32"; sm_len=%"PRIu32"\n", ctrl_len, sm_len);
                        bytes = sizeof(shared_buf_t) + 
                            sizeof(kvs_ht_reply_t) + ctrl_len + sm_len;
                        sh_buf = (shared_buf_t*)malloc(bytes);
                        if (NULL == sh_buf) {
                            error("malloc (%s)\n", strerror(errno));
                            terminate(1);
                        }
                        memset(sh_buf, 0, bytes);
                        sh_buf->len = bytes - sizeof(shared_buf_t);
                        reply = (kvs_ht_reply_t*)sh_buf->buf;
                        reply->type = REPLY_RC;
                        reply->rc = 0;
                        reply->u.join.csqn = consensus_sqn;
                        reply->u.join.sid = empty;
                        reply->u.join.n = data.n;
                        reply->u.join.rnines = data.rnines;
                        reply->u.join.ctrl_len = ctrl_len;
                        reply->len = ctrl_len + sm_len;
                        if (ctrl_len) {
                            create_kvs_ht_snapshot(data.ctrl_sm, 
                                                    reply->data);
                        }
#ifdef AC_KVS                        
                        if (sm_len) {
                            create_kvs_ht_snapshot(data.kvs, 
                                                reply->data + ctrl_len);
                        }
#endif                        
                        rv = reply_to_client(offset, sh_buf);
                        if (rv) {
                            error("reply_to_client\n");
                            terminate(1);
                        }
                    }

                    /* Get published ID of added server */
                    // TODO: how to avoid reading the previous ID? :(
                    // new servers connect to their successors and send 
                    // a PUBLISH message with their listening port; 
                    // if a server receives a PUBLISH message with different port it sends it further
#if 0
                    char filename[NAME_MAX];
                    sprintf(filename, "p%"PRIu32".id", empty);
                    while (1) {
                        if (access(filename, F_OK) != -1) {
                            break;
                        }
                    }
                    FILE *stream = fopen(filename, "r");
                    if (NULL == stream) {
                        error("cannot open server file %s\n", filename);
                        terminate(1);
                    }
                    char *word = NULL;
                    char line[LINE_MAX];
                    while (fgets(line, LINE_MAX, stream)) { 
                        /* Parse each line */
                        if (line[0] == '#') continue;
                        if (line[0] == '\n') continue;
                        /* Remove trailing newline */
                        line[strcspn(line, "\r\n")] = 0;
                        if (strcmp(line, "") == 0) {
                            if (!word) {
                                fseek(stream, 0, SEEK_SET);
                                continue;
                            }
                            else 
                                break;
                        }
                        memset(added_srv->srv_value->ni.ac_port, 0, 
                                sizeof added_srv->srv_value->ni.ac_port);
                        word = strtok(line," \t\r\n");
                        word = strtok(NULL," \t\r\n");
                        strcpy(added_srv->srv_value->ni.ac_port, word);
                    }
                    fclose(stream);
                    info_wtime("p%"PRIu32"'s ID -- %s:%s\n", empty, 
                            added_srv->srv_value->ni.host, added_srv->srv_value->ni.ac_port);
#endif                    
                   
                    /* Send connection request (if needed) */
                    if (UINT32_MAX != get_predecessor_idx(G, empty, data.self))
                    {
                        rv = connect_to(empty);
                        if (rv) {
                            error("connect_to\n");
                            terminate(1);
                        }
                    }
                    empty++;
                }
            }
next_request:
            offset += sizeof(kvs_ht_cmd_t) + cmd->key_len + cmd->value_len;
        }
    }
    if (!just_check) return;
    just_check = 0;
    goto loop_through_inputs;
}

#if 0
static uint32_t
apply_inputs_to_sm()
{
    kvs_ht_cmd_t *cmd = NULL;
    kvs_blob_t value;
    kvs_ht_reply_t *reply = NULL, no_data_reply;
    srv_t *srv = NULL;
    int rc;
    uint32_t offset, byte_count = 0, sid;
    uint64_t cmd_sqn;
    
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        if (!(SRV_INPUT & srv->state)) continue;
        /* Received non-empty input from this server */
        byte_count += srv->inlen;
        offset = 0;
        while (offset < srv->inlen) {
            cmd = (kvs_ht_cmd_t*)((uint8_t*)srv->input + offset);
            if (CTRL_JOIN == cmd->type) {
                goto next_request;
            }
            if (0 == cmd->cid.srv_sqn) {             
                /* Generate new CID */
                cmd_sqn = generate_new_cid(srv, &(cmd->cid));
                if (0 == cmd_sqn) {
                    error("generate_new_cid\n");
                    smr_terminate(1);
                }
//info_wtime("Generated new CID: %"PRIu64"-%"PRIu64"\n", cmd->cid.srv_sqn, cmd->cid.clt_sqn);
//print_kvs(data.ctrl_sm);
            }
            else {
                /* Check the command SQN */
                cmd_sqn = get_expected_sqn(data.ctrl_sm, 
                                        &cmd->cid);
                if (0 == cmd_sqn) {                    
                    /* This client no longer has an CID */
                    cmd_sqn = generate_new_cid(srv, &cmd->cid);
                    if (0 == cmd_sqn) {
                        error("generate_new_cid\n");
                        smr_terminate(1);
                    }
//info_wtime("Expired CID; Generated new CID: %"PRIu64"-%"PRIu64"\n", cmd->cid.srv_sqn, cmd->cid.clt_sqn);
                }
                else if (cmd_sqn != cmd->sqn) {
                    /* Wrong command SQN */
//info_wtime("Wrong SQN: expected=%"PRIu64" vs. actual=%"PRIu64"\n", cmd->sqn, cmd_sqn);
                    if (sid == data.self) {
                        /* Command from own client -- send notification */
                        memset(&no_data_reply, 0, sizeof(kvs_ht_reply_t));
                        no_data_reply.type = REPLY_RC;
                        no_data_reply.rc = 1;
                        no_data_reply.len = 0;
                        no_data_reply.u.sm.cid.srv_sqn = 
                                                cmd->cid.srv_sqn;
                        no_data_reply.u.sm.cid.clt_sqn = 
                                                cmd->cid.clt_sqn;
                        no_data_reply.u.sm.sqn = cmd_sqn;
                        rc = reply_to_client(offset, &no_data_reply);
                        if (0 != rc) {
                            error("reply_to_client\n");
                            smr_terminate(1);
                        }
                    }
                    goto next_request;
                }
            }
            
            /* Apply command */
            value.len = cmd->value_len;
            value.data = (void*)(cmd->data+cmd->key_len);
            rc = apply_kvs_ht_cmd(data.kvs, cmd->type, 
                    (const char*)cmd->data, &value, &reply);
            if (0 != rc) {
                error("apply_kvs_ht_cmd\n");
                smr_terminate(1);
            }
            rc = update_expected_sqn(data.ctrl_sm, &cmd->cid, cmd_sqn+1);
            if (0 != rc) {
                error("inc_expected_sqn\n");
                smr_terminate(1);
            }
            
            if (sid == data.self) {
                /* Command from own client -- reply */
                if (reply) {
                    reply->type = REPLY_RC;
                    reply->rc = 0;
                    reply->u.sm.cid.srv_sqn = cmd->cid.srv_sqn;
                    reply->u.sm.cid.clt_sqn = cmd->cid.clt_sqn;
                    reply->u.sm.sqn = cmd_sqn+1;
                    rc = reply_to_client(offset, reply);
                    if (0 != rc) {
                        error("reply_to_client\n");
                        smr_terminate(1);
                    }
                    free(reply);
                    reply = NULL;
                }
                else {
                    memset(&no_data_reply, 0, sizeof(kvs_ht_reply_t));
                    no_data_reply.type = REPLY_RC;
                    no_data_reply.rc = 0;
                    no_data_reply.len = 0;
                    no_data_reply.u.sm.cid.srv_sqn = cmd->cid.srv_sqn;
                    no_data_reply.u.sm.cid.clt_sqn = cmd->cid.clt_sqn;
                    no_data_reply.u.sm.sqn = cmd_sqn+1;
                    rc = reply_to_client(offset, &no_data_reply);
                    if (0 != rc) {
                        error("reply_to_client\n");
                        smr_terminate(1);
                    }
                }
            }
            goto next_request;
                        
next_request:
            offset += sizeof(kvs_ht_cmd_t) + cmd->key_len + cmd->value_len;
//info("<%s> %s\n", (char*)cmd->data, (char*)cmd->data+cmd->key_len);
        }
    }
    return byte_count;
//info("\n");
}
#endif 

static int
reply_to_client(uint32_t offset, shared_buf_t *sh_buf)
{
    ep_t *ep = NULL;
    client_t *client;
    int numbytes, rv;
    uint32_t in = rp_find_in(&data.request_pool, offset);
//info("Reply to CID: %"PRIu64"-%"PRIu64"\n",reply->u.sm.cid.srv_sqn, reply->u.sm.cid.clt_sqn);
 
    info("Send client reply (%"PRIu64" bytes)\n", sh_buf->len);   
    rv = cl_add_reply(in, sh_buf);
    if (rv) {
        error("cl_add_reply\n");
        return 1;
    }
    return 0;
}

static uint64_t
generate_new_cid(srv_t *srv, cid_t *cid)
{
    uint64_t cmd_sqn;
    
    cid->srv_sqn = srv->sqn;
    cid->clt_sqn = ++srv->srv_value->clt_sqn;
    cmd_sqn = add_client_to_ctrl_sm(data.ctrl_sm, cid);
    if (0 == cmd_sqn) {
        error("cannot add client\n");
        return 0;
    }
    return cmd_sqn;
}


/* ================================================================== */
/**
 * Remove server from array of servers
 */
static void 
remove_server(uint32_t sid)
{
    ep_t *ep;
    sid_queue_t *sq, *q;
    uint32_t i, degree = data.G[data.activeG]->degree;

    if (server_is_failed(sid)) {
        return;
    }

    /* Mark server as failed */
    set(&data.vertex_to_srv_map[sid].state, SRV_FAILED);
    unset(&data.vertex_to_srv_map[sid].state, SRV_GOT_MSG);
    unset(&data.vertex_to_srv_map[sid].state, SRV_MSG_LOST);

    /* Free list of failure notifications */
    sq = data.vertex_to_srv_map[sid].fn;
    while ((q = sq) != NULL) {
        sq = q->next;
        free(q);    
    }
    data.vertex_to_srv_map[sid].fn = NULL;
    
    data.vertex_to_srv_map[sid].srv_value->failed = 1;    
    /* If successor, remove it */
    ep = data.next_srv_list;
    while (NULL != ep) {
        next_srv_t *next_srv = (next_srv_t*)ep->data;
        if (next_srv->sid == sid) {
            ac_ep_destroy(ep);
            break;
        }
        ep = ep->next;
    }
    /* If predecessor, remove it */
    ep = data.prev_srv_list;
    while (NULL != ep) {
       prev_srv_t *prev_srv = (prev_srv_t*)ep->data;
       if (prev_srv->sid == sid) {
           ac_ep_destroy(ep);
           break;
       }
       ep = ep->next;
    }
}

static void
print_failure_notifications(uint32_t sid)
{
    sid_queue_t *sq;
    
    /* Print list of failure notifications */
    sq = data.vertex_to_srv_map[sid].fn;
    info_wtime("F[p%"PRIu32"]:", sid);
    while (sq != NULL) {
        info(" p%"PRIu32, sq->sid);
        sq = sq->next;
    }
    info("\n");
}


/* ================================================================== */

static void 
terminate_cb(EV_P_ ev_timer *w, int revents)
{
    /* Check whether all messages are sent */
    ep_t *ep = data.next_srv_list;
    while (NULL != ep) {
        conn_ctx_t *send_ctx = (conn_ctx_t*)ep->conn;
        next_srv_t *next_srv = (next_srv_t*)ep->data;
        if (send_ctx->send_buf) {
            info("Still sending to p%"PRIu32"\n", next_srv->sid);
            w->repeat = 0.5;
            ev_timer_again(EV_A_ w);
            return;
        }
        ep = ep->next;
    }

    terminate(0);
}

#ifdef BENCHMARK 
static void
throughput_cb(EV_P_ ev_timer *w, int revents)
{
    static uint32_t count = 0;    
#ifdef MSG_FLOW    
    info_wtime("Agreed on %d bytes; bytes waiting to be sent %"PRIu64"\n", 
            agreed_on_byte_count, ac_net_mod->bytes_to_send);
#endif
    /* Collect throughput data */
    if (bench_data.throughput_tail->idx == BENCH_BUF_LEN) {
        /* Buffer full; allocate a new one */
        bench_buf_double_t *tail = bench_data.throughput_tail;
        bench_data.throughput_tail = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
        if (!bench_data.throughput_tail) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(bench_data.throughput_tail, 0, sizeof(bench_buf_double_t));
        tail->next = bench_data.throughput_tail;
    }
    bench_data.throughput_tail->buf[bench_data.throughput_tail->idx] = 
                        1.*agreed_on_byte_count/throughput_out_period;
    bench_data.throughput_tail->idx++;
    agreed_on_byte_count = 0;

    if (AC_BENCH_LAT == bench_type || AC_BENCH_FAIL == bench_type) {
        return;
    }
    count++;
    if (count >= sample_size) {
        info_wtime("I'm done; %d throughput measurements (i.e., %lf sec)\n", 
                    sample_size, sample_size*throughput_out_period);
        bench_done = 1;
        ev_set_cb(w, terminate_cb);
        w->repeat = 1;
        ev_timer_again(EV_A_ w);
    }
}

static void
add_request_cb(EV_P_ ev_timer *w, int revents)
{
    int rv;

    /* Measure the time of an abcast round */
    if (timer) {
        HRT_TIMESTAMP_T *t_start = (HRT_TIMESTAMP_T*)request->data;
        HRT_GET_TIMESTAMP((*t_start));
    }

    rv = rp_add_request(&data.request_pool, 
                    request, data.req_size, NULL, 0, NULL);
    if (RP_FULL == rv) {
        info("The request pool is full; exit\n");
        w->repeat = 0;
        ev_timer_again(EV_A_ w);    
        terminate(1);
    }
    if ((AC_BENCH_LAT == bench_type) || (warmup)) {
        goto stop;
    }
    w->repeat = gen_t_req();
    ev_timer_again(EV_A_ w);
    return;
                 
stop:
    w->repeat = 0;
    ev_timer_again(EV_A_ w);    
}

static double
gen_t_req()
{
    /* Set seed */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    double rand_0_1 = drand48();
    double t_req = 1.*(data.t_req - data.t_req_err) +
            rand_0_1 * 2. * data.t_req_err;
    return t_req*0.001;
}

static void 
set_faulty_servers()
{
    uint32_t i;
    uint32_t sid, prev_sid;
    digraph_t *G = data.G[data.activeG];
    
    /* Set seed */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
    memset(faulty_servers, 0, data.n);
    if (failure_scenario == FAIL_RANDOM) {
        for (i = 0; i < fail_count;) {
            sid = (uint32_t)(lrand48() % (data.n-1) + 1);
            if (faulty_servers[sid]) {
                continue;
            }
            i++;
            faulty_servers[sid]=i;
info("FAILURE: p%"PRIu32"\n", sid);            
        }
    }
    else {
        sid = (uint32_t)(lrand48() % (data.n-1) + 1);
        faulty_servers[sid]=1;
        prev_sid = sid;
        for (i = 1; i < fail_count; i++) {
            sid = get_successor(G, prev_sid, 0);
            if (sid == 0) {
                sid = get_successor(G, prev_sid, 1);
            }
            faulty_servers[sid] = i+1;
            prev_sid = sid;
        }
    }
}

static void 
set_failing_point()
{
    digraph_t *G = data.G[data.activeG];
    
    /* Set seed */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
    failing_point = (uint32_t)(lrand48() % (data.n*G->degree-1) + 1);
}

static void
remove_self()
{
    uint32_t sid;
    srv_t *srv;
    uint32_t degree = data.G[data.activeG]->degree;
    consensus_sqn = start_hb_sqn;
    fd_stop();
    memset(data.sent_msgs, 0, (degree + 1)*data.n);
    sid_queue_t *sq = NULL;
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        /* Reset DONE flag */     
        unset(&srv->state, SRV_GOT_MSG);
        /* Reset MSG_LOST flag */
        unset(&srv->state, SRV_MSG_LOST);
        /* Reset INPUT flag */
        unset(&srv->state, SRV_INPUT);
        /* No need to free inputs */
        
        while ((sq = srv->fn) != NULL) {
            srv->fn = sq->next;
            free(sq);  
        }
    }
    info_wtime("I've failed\n");
}

static void benchmarking()
{ 
    srv_t *srv = NULL;
    kvs_ht_cmd_t *cmd = NULL;
    uint32_t offset;
    HRT_TIMESTAMP_T *t_start;
    uint64_t ticks;
    double usecs;
    uint64_t prev_round_sqn = consensus_sqn - 1;
    
    if (timer) {    
        HRT_GET_TIMESTAMP(t_round_end);
        HRT_GET_ELAPSED_TICKS(t_round_start, t_round_end, &ticks);
        usecs = HRT_GET_USEC(ticks);
    }

    HRT_GET_TIMESTAMP(tww[!ww_flag]);
    HRT_GET_ELAPSED_TICKS(tww[ww_flag], tww[!ww_flag], &ticks);
    ww_usecs[ww_flag] += HRT_GET_USEC(ticks);
#if 0
    info("### %s += %lf usecs\n", (ww_flag == WW_WAIT ? "waiting" : "working"), HRT_GET_USEC(ticks));
    if (ww_flag == WW_WAIT) {
        info("   poll_count=%"PRIu64"\n", poll_count);
    }
#endif    
    ww_flag = WW_NONE;

#if 0
    info_wtime("Reached consensus #%"PRIu64" (on %"PRIu32" bytes) "
            "(%"PRIu32" messages) in %9.3lf us (work=%9.3lf us; wait=%9.3lf us; send=%9.3lf us)"
            " recv_bytes=%"PRIu64",rx_bw=%lf, sent_bytes=%"PRIu64", tx_bw=%lf"
            ", avoid_redundant_count=%"PRIu32"\n\n", 
            prev_round_sqn, bench_data.byte_count, bench_data.srv_count, usecs,
            ww_usecs[WW_WORK], ww_usecs[WW_WAIT], send_usecs, 
            recv_bytes, .001 * recv_bytes * 8 / usecs, 
            sent_bytes, .001 * sent_bytes * 8 / usecs, 
            avoid_redundant_count);
    //if (prev_round_sqn > 5 && ww_usecs[WW_WORK] > 200) info("### WORK ###\n");
    avoid_redundant_count = 0;
#endif    
 
#ifdef MSG_FLOW    
    if (timer) {
        info_wtime("Reached consensus #%"PRIu64" (on %"PRIu32" bytes) "
            "(%"PRIu32" messages) in %9.3lf us\n\n", prev_round_sqn, 
            bench_data.byte_count, bench_data.srv_count, usecs);
//dump_bytes(data.vertex_to_srv_map[0].input, data.vertex_to_srv_map[0].inlen, "INPUT");
    }
    else {
        info_wtime("Reached consensus #%"PRIu64" (on %"PRIu32" bytes)\n\n", 
                    prev_round_sqn, bench_data.byte_count);
    }
#endif
   
    if (warmup) goto warming_up;   
    
    /* Measure the time of reaching agreement;
     * Note: do not collect round data for failure benchmark */
    if (timer && data.t_round_stream && AC_BENCH_FAIL != bench_type) {
        /* Collect round data */
        bench_buf_round_t *tail = NULL;
        if (bench_data.round_tail->idx == BENCH_BUF_LEN) {
            /* Buffer full; allocate a new one */
            tail = (bench_buf_round_t*)malloc(sizeof(bench_buf_round_t));
            if (!tail) {
                error("malloc (%s)\n", strerror(errno));
                terminate(1);
            }
            memset(tail, 0, sizeof(bench_buf_round_t));
            bench_data.round_tail->next = tail;
            bench_data.round_tail = tail;
        }
        else {
            tail = bench_data.round_tail;
        }
        tail->buf[tail->idx].round_sqn = prev_round_sqn;
        tail->buf[tail->idx].srv_count = bench_data.srv_count;
        tail->buf[tail->idx].byte_count = bench_data.byte_count;
        tail->buf[tail->idx].usecs = usecs;
        tail->buf[tail->idx].work = ww_usecs[WW_WORK];
        tail->buf[tail->idx].wait = ww_usecs[WW_WAIT];
        tail->buf[tail->idx].rx_bw = .001 * recv_bytes * 8 / usecs;
        tail->buf[tail->idx].tx_bw = .001 * sent_bytes * 8 / usecs;
        tail->idx++;
    }
   
    /* Measure the time to answer own requests;
     * Note: do not collect request data for neither failure nor throughput benchmarks */
    if (timer && data.t_request_stream && 
           AC_BENCH_THRP != bench_type && 
           AC_BENCH_FAIL != bench_type && 
           bench_data.request_tail->idx < BENCH_BUF_LEN) // avoid collecting too many request measurements
    {
        srv = &data.vertex_to_srv_map[data.self];
        if (SRV_INPUT & srv->state) {
            offset = 0;
            while (offset < srv->inlen) {
                cmd = (kvs_ht_cmd_t*)((uint8_t*)srv->input + offset);
                if (KVS_PUT == cmd->type) {
                    /* Collect request data */
                    t_start = (HRT_TIMESTAMP_T*)cmd->data;
                    HRT_GET_ELAPSED_TICKS((*t_start), t_round_end, &ticks);
                    if (bench_data.request_tail->idx == BENCH_BUF_LEN) {
                        /* Buffer full; allocate a new one */
                        bench_buf_double_t *tail = bench_data.request_tail;
                        bench_data.request_tail = (bench_buf_double_t*)malloc(sizeof(bench_buf_double_t));
                        if (!bench_data.request_tail) {
                            error("malloc (%s)\n", strerror(errno));
                            terminate(1);
                        }
                        memset(bench_data.request_tail, 0, sizeof(bench_buf_double_t));
                        tail->next = bench_data.request_tail;
                    }
                    bench_data.request_tail->buf[bench_data.request_tail->idx] = HRT_GET_USEC(ticks);
                    bench_data.request_tail->idx++;
                }
                offset += sizeof(kvs_ht_cmd_t) + cmd->key_len + cmd->value_len;
            }
        }
    }  
    
    /* Check whether to stop benchmarks */
    if ((AC_BENCH_LAT == bench_type &&                          /* latency benchmark */
            consensus_sqn >= sample_size + WARMUP_COUNT) ||     /* sample_size rounds */
        (AC_BENCH_REQ == bench_type &&                          /* request rate benchmark */
            consensus_sqn >= sample_size*10 + WARMUP_COUNT))    /* 10*sample_size rounds (avoid waiting for 100 sec) */
    {
        
        if (consensus_sqn >= sample_size + WARMUP_COUNT) {
            if (AC_BENCH_LAT == bench_type) {
                info_wtime("Latency benchmark completed; %d round measurements\n", sample_size);
            }
            else {
                info_wtime("Request rate benchmark completed; %d round measurements\n", 10*sample_size);
            }
            bench_done = 1;
            
            /* And schedule the termination callback */
            ev_set_cb(&w_throughput, terminate_cb);
            w_throughput.repeat = 0.5;
            ev_timer_again(data.loop, &w_throughput);
            return;
        }
    }
    else if (AC_BENCH_THRP == bench_type) {
        /* throughput benchmark */
        if (consensus_sqn >= throughput_rounds*(sample_size + WARMUP_COUNT)) {
#ifdef AVOID_REDUNDANT
            info_wtime("Done with %"PRIu32" (%"PRIu32"-byte) request messages (redundant_msgs=%"PRIu32")\n", 
                    batching_factor, data.req_size, avoid_redundant_count);
            avoid_redundant_count = 0;
#else            
info_wtime("Done with %"PRIu32" (%"PRIu32"-byte) request messages\n", batching_factor, data.req_size);
#endif
            if (batching_factor >= data.max_batching) {
                info_wtime("Throughput benchmark completed\n");
                bench_done = 1;
                /* And schedule the termination callback */
                ev_set_cb(&w_throughput, terminate_cb);
                w_throughput.repeat = 0.5;
                ev_timer_again(data.loop, &w_throughput);
                return;
            }
            
            /* Print round data -- in case of a problem it will be nice to have some data */
            print_round_data();

            /* Next message size */
            batching_factor *= 2;
            throughput_rounds++;
            warmup = WARMUP_COUNT+1;
        }
    }

warming_up:
    if (warmup) {
        warmup--;
#ifdef MSG_FLOW    
        info_wtime("WARMUP = %d\n", warmup); 
#endif
        if (0 == warmup) {
            /* Warmup is over */
#ifdef STATS
            ac_net_mod->total_recv_bytes = 0;
            ac_net_mod->receiving_time = 0;
            ac_net_mod->total_sent_bytes = 0;
            ac_net_mod->sending_time = 0;
#endif            
            if (data.throughput_stream && AC_BENCH_THRP != bench_type) {
                /* Start a watcher to measure throughput */
                w_throughput.repeat = throughput_out_period;
                ev_timer_again(data.loop, &w_throughput);
                agreed_on_byte_count = 0;
            }
            if (AC_BENCH_REQ == bench_type || AC_BENCH_FAIL == bench_type) {
                /* Start generating periodic requests */        
                //info("Done warming-up -- schedule periodic add_request callbacks\n");
                w_add_request.repeat = gen_t_req();
                ev_timer_again(data.loop, &w_add_request);
            }
        }
        else if (AC_BENCH_REQ == bench_type || AC_BENCH_FAIL == bench_type) {
            /* Start generating requests */
            //info("Warming-up -- schedule another add_request callback\n");
            w_add_request.repeat = timeout;
            ev_timer_again(data.loop, &w_add_request);
        }
    }
    
    if ((AC_BENCH_LAT == bench_type) && (data.self == 0)) {
        /* Start generating requests */
        w_add_request.repeat = timeout;
        ev_timer_again(data.loop, &w_add_request);
    }

}

static void
print_round_data()
{
    uint32_t i;
    /* Print round data */
    if (data.t_round_stream) {
        bench_buf_round_t *bench_buf;
        if (!bench_data.round_head)
            return;
        while (1) {
            bench_buf = bench_data.round_head;
            for (i = 0; i < bench_buf->idx; i++) {
                fprintf(data.t_round_stream, "%12"PRIu64"   %5"PRIu32"   %8"PRIu32"   %9.3lf   %9.3lf   %9.3lf   %9.3lf   %9.3lf   %9.3lf   %9.3lf\n", 
                   bench_buf->buf[i].round_sqn, bench_buf->buf[i].srv_count,
                   bench_buf->buf[i].byte_count, bench_buf->buf[i].usecs,
                   bench_buf->buf[i].work, bench_buf->buf[i].wait,
                   .001 * bench_buf->buf[i].byte_count * 8 / bench_buf->buf[i].usecs,
                   bench_buf->buf[i].rx_bw, bench_buf->buf[i].tx_bw, bench_buf->buf[i].rx_bw+ bench_buf->buf[i].tx_bw);
            }
            if (NULL != bench_buf->next) {
                /* Go to next measurement */
                bench_data.round_head = bench_buf->next;
                free(bench_buf);
            }
            else {
                /* Reset queue */
                memset(bench_data.round_head, 0, sizeof(bench_buf_round_t));
                bench_data.round_tail = bench_data.round_head;
                break;
            }
        }
    }
}

#endif

#endif
