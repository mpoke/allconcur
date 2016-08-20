/**                                                                                                      
 * AllConcur
 * 
 * Network module
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef AC_NET_H
#define AC_NET_H

#include <stdlib.h>
#include <sys/socket.h>
#include <netdb.h>
#include <fcntl.h>
#include <ev.h>

#include <debug.h>
 
#define AC_NET_IBV  1
#define AC_NET_TCP  2

//#define MAX_OUTSTANDING 2048
#define MAX_OUTSTANDING 32
#define MAX_CONNECTIONS 64
//#define MAX_BUF_SIZE 4194304 // 4MiB
#define MAX_BUF_SIZE 4195328 // 32 x (128k+32)-byte messages ~ 4MiB
//#define MAX_BUF_SIZE 8390656 // 64 x (128k+32)-byte messages ~ 8MiB

#define MTU_MSG_SIZE 1500


#ifdef BENCHMARK
#define STATS
#endif

/* ================================================================== */
/* Endpoint */
typedef struct ep_t ep_t;

/* Endpoint identifier */
struct ep_id_t {
    char host[NI_MAXHOST];
    char port[NI_MAXSERV];
};
typedef struct ep_id_t ep_id_t;

/* Connection data */
struct conn_data_t {
    ep_id_t ei;                                         /* enpoint ID */
    int rcount;                             /* # receive WR / buffers */
    uint32_t rbuf_len;                      /* size of receive buffer */
    int scount;                                /* # send WR / buffers */
    uint32_t sbuf_len;                         /* size of send buffer */

    
    void* (*on_connection)(void*);
    void (*destroy_ep_data)(void*);
    void (*handle_data)(void*, void*, uint32_t);
};
typedef struct conn_data_t conn_data_t;

/* Enpoint */
struct ep_t {
    conn_data_t cd;
    int connected;
    int mtu_sent;
    ep_t *prev, *next;
    ep_t **head;
    void *conn;
    void *data;
};

/* UD setup */
struct ud_t {
    conn_data_t cd;
    void *conn;
    struct {
        uint32_t len;
        void *endpoint;
    } ud_info;
};
typedef struct ud_t ud_t;

/* ================================================================== */
/* ep->conn (at least partially) */

/* Shared buffer */
struct shared_buf_t {
    uint64_t len;
    uint32_t shared_count;
    uint32_t pad;
    uint8_t buf[0];
};
typedef struct shared_buf_t shared_buf_t;

/* Send buffer */
struct send_buf_t {
    shared_buf_t *sh_buf;
    uint64_t bytes_sent;
    uint8_t state;
    struct send_buf_t *next;
    struct send_buf_t *prev;
};
typedef struct send_buf_t send_buf_t;

/* Connection context */
struct conn_ctx_t {
    union {
        struct {
            ev_io io;
        } tcp;
        struct {
        } ib;
    } proto;
    ep_t *ep;
    ud_t *ud;
    send_buf_t *send_buf;
    int outstanding_sends;
    int buffering;
    int active;
};
typedef struct conn_ctx_t conn_ctx_t;

/* ================================================================== */

struct ac_net_module_t {
    char *name;
    char *desc;
    uint64_t bytes_to_send;
    struct ev_loop *ev_loop;
    int timer;
    uint64_t total_sent_bytes;
    double sending_time;
    uint64_t total_recv_bytes;
    double receiving_time;
    
    /* Terminate function */
    void (*terminate)(int);    
   
    /* Get send buffer */
    void* (*get_sbuf)(void *conn_id, int *idx);
   
    /* Get send buffer length */
    int (*get_sbuf_len)(void *conn_id);
   
    /* Synchronous connect */
    int (*connect)(ep_t* ep);
   
    /* Synchronous send */
    int (*send)(void *conn_id, void *buf_idx, uint32_t len);
   
    /* Synchronous receive */
    int (*receive)(void *conn_id, void *recv_buf, uint32_t len);
   
    /* Disconnect */
    void (*disconnect)(void *conn_id);
    
    /* Disconnect all */
    void (*wait_for_disconnects)(void *ch);
   
    /* Asynchronous listen */
    void* (*ilisten)(conn_data_t *cd);
    
    /* Asynchronous connect */
    int (*iconnect)(ep_t* ep, void *channel);
    
    /* Polling on a channel */
    int (*poll_ch)(void *ch);
    
    /* Polling on an incoming connection */
    int (*poll_recv)(ep_t *ep);
                    
    /* Asynchronous send */
    int (*isend)(ep_t *ep, shared_buf_t *sh_buf);
    
    /* Polling for send completion */
    int (*poll_send)(ep_t *ep);

    /* Check whether sending buffers are empty */
    int (*done_sending)(ep_t *ep);
    
    /* Return the amount of bytes still in progress of being sent 
     * or whether there are still bytes in progress (IBV) */
    int (*ongoing_bytes)(ep_t *ep);

    /* Callback for when all data was sent */
    void (*on_send_completed)();
   
    /* Create channel */
    void* (*create_ch)();
    
    /* Destroy channel */
    void (*destroy_ch)(void *ch);
    
    /* Setup unreliable datagrams */
    int (*ud_setup)(ud_t* ud);
    
    /* Send datagram */
    int (*sendto)(ud_t* ud, void *endpoint, void *buf, uint32_t buf_len);
    
    /* Polling for sendto completion */
    int (*poll_sendto)(ud_t* ud);
    
    /* Polling for unreliable datagrams */
    int (*ud_poll_recv)(ud_t *ud);
    
    /* Compare two UD endpoints */
    int (*cmp_ud_eps)(void *left, void *right);
    
    /* Copy a UD endpoint */
    int (*cp_ud_ep)(void **dest, void *src);
    
    /* UD endpoint to string */
    char* (*ud_ep_to_str)(char *str, uint32_t len, void *endpoint);
    
    /* Print an UD endpoint */
    void (*print_ud_ep)(void *endpoint);
};
typedef struct ac_net_module_t ac_net_module_t;
extern ac_net_module_t *ac_net_mod;

/**
 * Set / unset the O_NONBLOCK for sockets
 */
static inline int 
set_blocking(int sfd, int do_block)
{
    int flags;
    flags = fcntl(sfd, F_GETFL, 0);
    if (-1 == flags) {
        error("fcntl (%s)\n", strerror(errno));
        return 1;
    }
    if (do_block) {
        /* blocking */
        flags &= ~O_NONBLOCK;
        if (-1 == fcntl(sfd, F_SETFL, flags)) {
            error("fcntl (%s)\n", strerror(errno));
            return 1;
        }
    }
    else {
        /* non-blocking */
        flags |= O_NONBLOCK;
        if (-1 == fcntl(sfd, F_SETFL, flags)) {
            error("fcntl (%s)\n", strerror(errno));
            return 1;
        }
    }
    return 0;
}

static inline void
ac_ep_add(ep_t* ep)
{
    if (!ep->head) return;
    
    ep->prev = NULL;
    ep->next = *(ep->head);
    if (ep->next) 
        ep->next->prev = ep;
    *(ep->head) = ep;
}

static inline void 
ac_ep_destroy(ep_t *ep)
{
    if (!ep) return;
    if (ep->cd.destroy_ep_data)
        ep->cd.destroy_ep_data(ep->data);
    if (ep->conn) {
        conn_ctx_t *conn_ctx = (conn_ctx_t*)ep->conn;
        conn_ctx->ep = NULL;
        ac_net_mod->disconnect(ep->conn);
    }
    if (ep->next) ep->next->prev = ep->prev;
    if (ep->prev) {
        ep->prev->next = ep->next;
    }
    else if (ep->head) *(ep->head) = ep->next;
    free(ep);
}

static inline int 
ac_handle_ep_error(ep_t *ep)
{
    int rv;
    if (!ep) return 0;
    conn_ctx_t *conn_ctx = (conn_ctx_t*)ep->conn;
    if (!conn_ctx) {
        error("conn is NULL\n");
        return 1;
    }
    if (conn_ctx->active) {
        /* Outgoing connection -- try to reconnect */
        //info_wtime("Outgoing connection -- reconnect\n");
        ep->connected = 0;
        rv = ac_net_mod->iconnect(ep, NULL);
        if (rv) {
            error("ac_ibv_iconnect\n");
            return 1;
        }
    }
    else {
        /* Incoming connection -- destroy connection */
        //info_wtime("Incoming connection -- destroy\n");
        ac_ep_destroy(ep);
    } 
    return 0;
}

#endif /* AC_NET_H */
