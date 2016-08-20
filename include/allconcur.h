/**                                                                                                      
 * AllConcur
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef ALLCONCUR_H
#define ALLCONCUR_H

#include <pthread.h>
#include <limits.h>

#include <digraph.h>
#include <ac_timer.h>

#include <kvs_ht.h>
#include <ac_ep.h>
#include <ac_types.h>
#include <ac_fd.h>
#include <g_array.h>
#include <request_pool.h>
#include <ac_net.h>

//#define AC_KVS

/* For immediate event scheduling */
#define NOW 0.0000001

#define EPSTR_LEN 64

#ifdef BENCHMARK
#define AC_BENCH_REQ    0
#define AC_BENCH_LAT    1
#define AC_BENCH_THRP   2
#define AC_BENCH_FAIL   3
#endif

//#define AVOID_REDUNDANT

//#define MSG_FLOW    

//#define MSG_DELAY

extern int detector_pid;
extern int join;
extern int net_type;
#ifdef BENCHMARK 
extern int bench_type;
#endif 
extern uint64_t consensus_sqn;

extern uint64_t poll_count;

extern tuple_t *tuple_queue;

struct fd_t {
    double timeout;                          /* normal timeout period */
    double warmup;                  /* timeout period for new servers */
    double hb_period;                        /* period of sending HBs */
    ud_t ud;
    
    pthread_mutex_t next_mutex;
    pthread_cond_t cond;
    int stop_sending;    
    fd_ep_t *next_srv;
    
    pthread_mutex_t prev_mutex;
    int failure;
    fd_ep_t *prev_srv;
    int error;
};
typedef struct fd_t fd_t;

struct data_t { 
    /* Configuration data */
    char *srv_file;
    net_id_t self_ni;                                /* own server ID */
    uint32_t self;                                /* own server index */
    uint32_t outstanding;
    uint32_t max_buf_size;
#ifdef BENCHMARK
    FILE *throughput_stream;
    FILE *t_round_stream;
#ifdef MSG_DELAY    
    FILE *delay_stream;
#endif    
    FILE *t_request_stream;
    double t_req;                        /* request generating period */
    double t_req_err;              /* request generating period error */
    uint32_t req_size;                                /* request size */
    uint32_t max_batching;                     /* max batching factor */
#endif

    /* libev data */
    struct ev_loop *loop;                      /* loop for EV library */
    ev_idle w_poll;                       /* Idle watcher for polling */
    
    /* Channels */
    void *prev_srv_ch;
    void *next_srv_ch;
    void *client_ch;
    
    /* AllConcur data */
    uint32_t n;                                  /* number of servers */
    srv_t *vertex_to_srv_map;              /* vertexes to servers map */
    uint32_t rnines;                 /* reliability (k-nine notation) */
    digraph_t *G[2];             /* regular digraphs (old and active) */
    int activeG;                   /* indicator of the active digraph */
    ep_t *next_srv_list;                        /* list of successors */
    ep_t *prev_srv_list;                      /* list of predecessors */
    uint8_t *sent_msgs;                 /* for tracking sent messages */
    request_pool_t request_pool;                      /* request pool */
    g_array_t *g_array;                        /* array of digraphs g */
    ep_t *ac_srv_list;        /* list of AllConcur servers (for JOIN) */
    
    /* State Machines */
    kvs_ht_t *ctrl_sm;                                  /* control SM */
    kvs_ht_t *kvs;                             /* state machine (KVS) */
        
    pthread_mutex_t quit_mutex;                         /* quit mutex */
    
    /* Failure Detector (FD) */
    pthread_t fd_thread;                                 /* FD thread */
    fd_t fd;                                               /* FD data */
    
    /* Client listener */
    pthread_t c_listener;
    pthread_mutex_t clt_mutex;
    ep_t *client_list;                             /* list of clients */
    char clt_port[NI_MAXSERV];               /* client listening port */
};
typedef struct data_t data_t;
extern data_t data;

static inline void
set(uint32_t *x, uint32_t flag)
{
    //~ info("##### set (flag = %"PRIu32") X: %"PRIu32" vs. ", flag, *x);
    (*x) |= flag;
    //~ info("%"PRIu32"\n", *x);
}
static inline void
unset(uint32_t *x, uint32_t flag)
{
    //~ info("##### unset (flag = %"PRIu32") X: %"PRIu32" vs. ", flag, *x);
    (*x) &= ~flag;
    //~ info("%"PRIu32"\n", *x);
}

static inline int 
quit(pthread_mutex_t *mtx)
{
    switch(pthread_mutex_trylock(mtx)) {
    case 0:
        pthread_mutex_unlock(mtx);
        return 1;
    case EBUSY:
        return 0;
    }
    return 1;
}

void terminate(int rc);
int connect_to(uint32_t sid);

#endif /* ALLCONCUR_H */
