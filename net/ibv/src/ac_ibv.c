/**                                                                                                      
 * AllConcur
 * 
 * Network module -- RDMA-CM
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <unistd.h>
#include <rdma/rdma_verbs.h>

#include <debug.h>
#include <ac_timer.h>
#include <ac_net.h>
#include <ac_ibv.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define mtu_value(mtu) \
    ((mtu == IBV_MTU_256) ? 256 :    \
    (mtu == IBV_MTU_512) ? 512 :    \
    (mtu == IBV_MTU_1024) ? 1024 :  \
    (mtu == IBV_MTU_2048) ? 2048 :  \
    (mtu == IBV_MTU_4096) ? 4096 : 0)

#define qp_state_to_str(state) \
   ((state == IBV_QPS_RESET) ? "RESET" : \
   (state == IBV_QPS_INIT) ? "INIT" : \
   (state == IBV_QPS_RTR) ? "RTR" : \
   (state == IBV_QPS_RTS) ? "RTS" : \
   (state == IBV_QPS_ERR) ? "ERR" : "X")

#define TIMEOUT_IN_MS 500

/* Return code for handling WCs */
#define WC_SUCCESS      0
#define WC_ERROR        1
#define WC_FAILURE      2
#define WC_SOFTWARE_BUG 3

#define RC_SEND_MAX_LEN (1 << 31)

struct reg_mem_t {
    uint32_t        len;
    uint8_t         *buf;
    int             avail;
    struct ibv_mr   *mr;
    struct ibv_ah   *ah;
    uint32_t in, out;
    int full;
};
typedef struct reg_mem_t reg_mem_t;

struct device_t {
    struct ibv_context *context;
    struct ibv_device_attr dev_attr;
    struct ibv_pd *pd;
    struct ibv_cq *scq;
    int scqe;
    struct ibv_cq *rcq;
    int rcqe;
    uint32_t max_inline_data;
    uint32_t mtu;
    uint16_t lid;
    uint16_t pkey_index;
    uint8_t port_num;
};
typedef struct device_t device_t;

struct conn_t {
    conn_ctx_t conn_ctx;
    device_t device;
    struct rdma_cm_id *id;
    struct ibv_qp *qp;
    int init_disconnect;
    
    uint32_t    sbuf_len;
    reg_mem_t   *send_mem;
    uint32_t    rbuf_len;
    reg_mem_t   *recv_mem;
};
typedef struct conn_t conn_t;

struct channel_t {    
    struct rdma_event_channel *ec;
    int disconnects_left;
    conn_data_t *cd;
    struct rdma_cm_id *id;
};
typedef struct channel_t channel_t;

struct ud_ep_t {
    uint16_t lid;
    uint32_t qpn;
};
typedef struct ud_ep_t ud_ep_t;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

/* Setters and getters */
static void* 
ac_ibv_get_sbuf(void *conn_id, int *idx);
static int 
ac_ibv_get_sbuf_len(void *conn_id);

/* Synchronous operations */
static int 
ac_ibv_connect(ep_t* ep);
static int 
ac_ibv_send(void *conn_id, void *buf_idx, uint32_t len);
static int
ac_rdma_recv(void *conn_id, void *recv_buf, uint32_t len);
static void 
ac_ibv_disconnect(void *conn_id);

/* Asynchronous operations */
static void* 
ac_ibv_ilisten(conn_data_t *cd);
static int 
ac_ibv_iconnect(ep_t* ep, void *channel);
static int 
ac_ibv_poll_ch(void *ch);
static int 
ac_ibv_poll_recv(ep_t *ep);
static int 
ac_ibv_isend(ep_t *ep, shared_buf_t *sh_buf);
static int 
ac_ibv_poll_send(ep_t *ep);
static int 
ac_ibv_done_sending(ep_t *ep);
static int 
ac_ibv_ongoing_bytes(ep_t *ep);
static void*
ac_ibv_create_ch();                    
static void
ac_ibv_destroy_ch(void *ch);
static void 
ac_ibv_wait_for_disconnects(void *ch);

/* Unreliable datagrams */
static int
ac_ibv_ud_setup(ud_t* ud);
static int 
ac_ibv_sendto(ud_t* ud, void *endpoint, void *buf, uint32_t buf_len);
static int 
ac_ibv_poll_sendto(ud_t* ud);
static int 
ac_ibv_ud_poll_recv(ud_t *ud);
static int 
ac_ibv_cmp_ud_eps(void *left, void *right);
static int 
ac_ibv_cp_ud_ep(void **dest, void *src);
static char*
ac_ibv_ud_ep_to_str(char *str, uint32_t len, void *endpoint);
static void
ac_ibv_print_ud_ep(void *endpoint);


/* Others */
static int
init_device(device_t *dev, int scqe, int rcqe);
static int
test_qp_support_rc(struct ibv_context *device_context);
static int 
on_connect_request(struct rdma_cm_id *id, 
                   conn_data_t *cd, 
                   struct rdma_conn_param *cm_params);
static int 
on_addr_resolved(struct rdma_cm_id *id);
static void 
set_buffer_len(conn_t *conn, conn_data_t *cd, int is_ud);
static int
register_memory(conn_t *conn, int is_ud);
static void
deregister_memory(conn_t *conn);
static int
post_receives(conn_t *conn);
static int
post_one_receive(conn_t *conn, int idx);
static void
disconnect(struct rdma_cm_id *id);
static void 
destroy_connection(conn_t *conn);
static void 
destroy_qp(conn_t *conn);
static int
handle_work_completion(conn_t *conn, struct ibv_wc *wc);
static int 
find_max_inline(struct ibv_context *context, 
                struct ibv_pd *pd,
                uint32_t *max_inline_arg);
                
#endif

/* ================================================================== */
/* Global variables */
#if 1

/* module registration data structure (IBV) */
ac_net_module_t ac_ibv_mod = {
    .name            = "IBV",
    .desc            = "Mode ibv uses IB verbs for data transmission.",
    .bytes_to_send   = 0,   
    .ev_loop         = NULL,
    .terminate       = NULL,
    .get_sbuf        = ac_ibv_get_sbuf,
    .get_sbuf_len    = ac_ibv_get_sbuf_len,
    .connect         = ac_ibv_connect,
    .send            = ac_ibv_send,
    .receive         = ac_rdma_recv,
    .disconnect      = ac_ibv_disconnect,
    .ilisten         = ac_ibv_ilisten,
    .iconnect        = ac_ibv_iconnect,
    .poll_ch         = ac_ibv_poll_ch,
    .poll_recv       = ac_ibv_poll_recv,
    .isend           = ac_ibv_isend,
    .poll_send       = ac_ibv_poll_send,
    .done_sending    = ac_ibv_done_sending,
    .ongoing_bytes   = ac_ibv_ongoing_bytes,
    .on_send_completed = NULL,
    .create_ch       = ac_ibv_create_ch,
    .destroy_ch      = ac_ibv_destroy_ch,
    .wait_for_disconnects = ac_ibv_wait_for_disconnects,
    .ud_setup        = ac_ibv_ud_setup,
    .sendto          = ac_ibv_sendto,
    .poll_sendto     = ac_ibv_poll_sendto,
    .ud_poll_recv    = ac_ibv_ud_poll_recv,
    .cmp_ud_eps      = ac_ibv_cmp_ud_eps,
    .cp_ud_ep        = ac_ibv_cp_ud_ep,
    .ud_ep_to_str    = ac_ibv_ud_ep_to_str,
    .print_ud_ep     = ac_ibv_print_ud_ep,
};

#endif

/* ================================================================== */
/* Global functions */
#if 1

void ac_ibv_reg_module(struct ev_loop *loop, 
                       void (*terminate)(int), 
                       int timer, 
                       void (*on_send_completed)())
{
    ac_net_mod = &ac_ibv_mod;
    ac_net_mod->ev_loop = loop;
    ac_net_mod->terminate = terminate;
    ac_net_mod->timer = timer;
    ac_net_mod->on_send_completed = on_send_completed;
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

/* ================================================================== */
/* Setters and getters */
static void* 
ac_ibv_get_sbuf(void *conn_id, int *idx)
{
    int i;
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return NULL;
    }
    for (i = 0; i < conn->device.scqe; i++) {
        if (conn->send_mem[i].avail) {
            conn->send_mem[i].avail = 0;
            if (idx) *idx = i;
            return conn->send_mem[i].buf;
        }
    }
    return NULL;
}

static int 
ac_ibv_get_sbuf_len(void *conn_id)
{
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return 1;
    }
    return conn->sbuf_len;
}

/* ================================================================== */
/* Synchronous operations */
/**
 * Connect to a remote host (synchronous)
 */
static int 
ac_ibv_connect(ep_t* ep)
{ 
    struct rdma_addrinfo *servinfo, hints;
    int rv;
    conn_t *conn = NULL;
    
    if (NULL == ep) {
        error("endpoint is NULL");
        return 1;
    }
    
    if (!ep->conn) goto new_connection;

    conn = (conn_t*)ep->conn;
    if (!conn->id) {
        error("existing connection, but no ID\n");
        return 1;
    }
    destroy_connection(ep->conn);
    ep->conn = conn = NULL;

new_connection:    
    /* Create connection */
    ep->conn = conn = (conn_t*)malloc(sizeof(conn_t));
    if (!conn) {
        error("malloc\n");
        return 1;
    }
    memset(conn, 0, sizeof(conn_t));
    conn->conn_ctx.active = 1;
    conn->conn_ctx.ep = ep;
        
    rv = rdma_create_id(NULL, &conn->id, NULL, RDMA_PS_TCP);    
    if (rv) {
        VERB_ERR("rdma_create_id", rv);
        goto cleanup;
    }
    conn->id->context = conn;
        
    memset(&hints, 0, sizeof (hints));
    hints.ai_port_space = RDMA_PS_TCP;
    rv = rdma_getaddrinfo(ep->cd.ei.host, ep->cd.ei.port, &hints, &servinfo);
    if (rv) {
        VERB_ERR("rdma_getaddrinfo", rv);
        goto cleanup;
    }
    
    rv = rdma_resolve_addr(conn->id, NULL, servinfo->ai_dst_addr, 2000);
    if (rv) {
        VERB_ERR("rdma_resolve_addr", rv);
        goto cleanup;
    }
    
    rv = on_addr_resolved(conn->id);
    if (rv) {
        VERB_ERR("on_addr_resolved", rv);
        goto cleanup;
    }
    
    struct rdma_conn_param cm_params;
    memset(&cm_params, 0, sizeof(cm_params));
    rv = rdma_connect(conn->id, &cm_params);
    if (rv) {
        VERB_ERR("rdma_connect", rv);
        goto cleanup;
    }
    rv = 0;
    goto cleanup;
    
cleanup:    
    if (servinfo) {
        rdma_freeaddrinfo(servinfo);
    }
    return rv;
}

static int 
ac_ibv_send(void *conn_id, void *buf_idx, uint32_t len)
{
    int rv;
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return 1;
    }
    struct ibv_send_wr wr, *bad_wr = NULL;
    struct ibv_sge sge;
    if (!buf_idx) {
        error("no index\n");
        return 1;
    }
    int *idx = (int*)buf_idx;

    memset(&wr, 0, sizeof(wr));
    wr.wr_id = (uintptr_t)(*idx);
    wr.opcode = IBV_WR_SEND;
    wr.sg_list = &sge;
    wr.num_sge = 1;
    wr.send_flags = IBV_SEND_SIGNALED;
    if (len <= conn->device.max_inline_data) {
        wr.send_flags |= IBV_SEND_INLINE;
    }

    sge.addr = (uintptr_t)conn->send_mem[*idx].buf;
    sge.length = len;
    sge.lkey = conn->send_mem[*idx].mr->lkey;

    rv = ibv_post_send(conn->qp, &wr, &bad_wr);
    if (rv) {
        VERB_ERR("ibv_post_send", rv);
        return 1;
    }
    
    /* Wait for send operation to complete */
    struct ibv_wc wc;
    int num_comp;
     
    do {
        num_comp = ibv_poll_cq(conn->device.scq, 1, &wc);
    } while (num_comp == 0);
      
    if (num_comp < 0) {
        VERB_ERR("ibv_poll_cq", rv);
        return 1;
    }
       
    /* Verify the completion status */
    if (wc.status != IBV_WC_SUCCESS) {
        error("Failed status %s (%d) for wr_id %d\n", 
             ibv_wc_status_str(wc.status), wc.status, (int)wc.wr_id);
        return 1;
    }

    return 0;    
}

static int 
ac_rdma_recv(void *conn_id, void *recv_buf, uint32_t len)
{
    int rv, ne;
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return 1;
    }
    if (!recv_buf) {
        error("no buffer\n");
        return 1;
    }
    struct ibv_mr *recv_mr = NULL;
    struct ibv_wc wc;
    uint8_t *buf = (uint8_t*)recv_buf;
    
    while (1) {
        ne = ibv_poll_cq(conn->device.rcq, 1, &wc);
        if (ne < 0) {
            VERB_ERR("ibv_poll_cq", rv);
            return 1;
        }
        if (ne == 0) {
            continue;
        }
        rv = handle_work_completion(conn, &wc);
        if (rv != WC_SUCCESS) {
            error("Completion with status 0x%x was found\n", wc.status);
            return 1;
        }
#if 0     
info("recv: wr_id=%"PRIu64", byte_len=%"PRIu32"\n", wc.wr_id, wc.byte_len);
dump_bytes(conn->recv_mem[wc.wr_id].buf, wc.byte_len, "RECV_DATA");
#endif
        /* Received data into buffer conn->recv_mem[wc->wr_id].buf */
        if (len > wc.byte_len) {
            memcpy(buf, conn->recv_mem[wc.wr_id].buf, wc.byte_len);
            buf += wc.byte_len;
            len -= wc.byte_len;
        }
        if (len != wc.byte_len) {
            error("multiple messages in one receive\n");
            return 1;
        }
        else {
            memcpy(buf, conn->recv_mem[wc.wr_id].buf, len);
            len = 0;
        }
        
        /* Post another receive */
        rv = post_one_receive(conn, wc.wr_id);
        if (rv) {
            error("post_one_receive\n");
            return 1;
        }
        if (!len) break;
    }
    return 0;
}

static void 
ac_ibv_disconnect(void *conn_id)
{
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) return;
    
    if (conn->id) {
        disconnect(conn->id);
    }
    else {
        destroy_connection(conn);
    }
}

/* ================================================================== */
/* Asynchronous operations */
/** 
 * Listen for incoming RC connections
 */
static void* 
ac_ibv_ilisten(conn_data_t *cd)
{
    int rv, port_num;
    ep_id_t ei;
    struct rdma_addrinfo *servinfo, hints, *p = NULL;
    channel_t *channel = NULL;
    struct rdma_event_channel *ec = NULL;
       
    channel = (channel_t*)ac_ibv_create_ch();
    if (NULL == channel) {
        error("ac_ibv_create_ch\n");
        return NULL;
    }
    channel->cd = malloc(sizeof(conn_data_t));
    if (!channel->cd) {
        error("malloc\n");
        goto exit_with_error;
    }
    memcpy(channel->cd, cd, sizeof(conn_data_t));
    
    rv = rdma_create_id(channel->ec, &channel->id, NULL, RDMA_PS_TCP);
    if (rv) {
        VERB_ERR("rdma_create_id", rv);
        goto exit_with_error;
    }
    
    while(!p) {
        memset(&hints, 0, sizeof (hints));
        hints.ai_port_space = RDMA_PS_TCP;
        hints.ai_flags = RAI_PASSIVE;
        rv = rdma_getaddrinfo(NULL, cd->ei.port, &hints, &servinfo);
        if (rv) {
            VERB_ERR("rdma_getaddrinfo", rv);
            goto exit_with_error;
        }
        
        for(p = servinfo; p != NULL; p = p->ai_next) {
            rv = rdma_bind_addr(channel->id, p->ai_src_addr);
            if (rv) {
                VERB_ERR("rdma_bind_addr", rv);
                rv = getnameinfo(p->ai_src_addr, p->ai_src_len, ei.host, NI_MAXHOST,
                                ei.port, NI_MAXSERV, NI_NUMERICSERV);
                info("Warning: bind to %s:%s (%s)\n", ei.host, ei.port, strerror(errno));
                continue;
            }
            break;
        }
        if (!p) {
            port_num = atoi(cd->ei.port);
            memset(cd->ei.port, 0, sizeof cd->ei.port);
            sprintf(cd->ei.port, "%d", (port_num+1));
            info("Could not bind to port %d; try port %s\n", port_num, cd->ei.port);
        }
    }
#if 0       
    rv = getnameinfo(p->ai_src_addr, p->ai_src_len, ei.host, NI_MAXHOST,
                            ei.port, NI_MAXSERV, NI_NUMERICSERV);
    info_wtime("Listening on %s:%s\n", ei.host, ei.port);
#endif    
    
    rv = rdma_listen(channel->id, MAX_CONNECTIONS);
    if (rv) {
        VERB_ERR("rdma_listen", rv);
        goto exit_with_error;
    }
    goto cleanup;
    
exit_with_error:
    ac_ibv_destroy_ch(channel);
    channel = NULL;
cleanup:    
    if (servinfo) {
        rdma_freeaddrinfo(servinfo);
    }
    return channel;    
}

static int 
ac_ibv_iconnect(ep_t* ep, void *ch)
{
    int rv;
    struct rdma_addrinfo *servinfo, hints;
    conn_t *conn = NULL;
    channel_t *channel;
    struct rdma_event_channel *ec = NULL;
    
    if (NULL == ep) {
        error("endpoint is NULL");
        return 1;
    }

    if (!ep->conn) goto new_connection;

    //info("# existing connection\n");
    conn = (conn_t*)ep->conn;
    if (!conn->id) {
        error("existing connection, but no ID\n");
        return 1;
    }
    ec = conn->id->channel;
    destroy_connection(conn);
    ep->conn = conn = NULL;

new_connection:    
    /* Create connection */
    if (!ch && !ec) {
        error("no channel");
        return 1;
    }
    if (!ec) {
        channel = (channel_t*)ch;
        ec = channel->ec;
    }

    ep->conn = conn = (conn_t*)malloc(sizeof(conn_t));
    if (!conn) {
        error("malloc\n");
        return 1;
    }
    memset(conn, 0, sizeof(conn_t));
    conn->conn_ctx.active = 1;
    conn->conn_ctx.ep = ep;
        
    rv = rdma_create_id(ec, &conn->id, NULL, RDMA_PS_TCP);    
    if (rv) {
        VERB_ERR("rdma_create_id", rv);
        goto cleanup;
    }
    conn->id->context = conn;
    
    memset(&hints, 0, sizeof (hints));
    hints.ai_port_space = RDMA_PS_TCP;
    rv = rdma_getaddrinfo(ep->cd.ei.host, ep->cd.ei.port, &hints, &servinfo);
    if (rv) {
        VERB_ERR("rdma_getaddrinfo", rv);
        goto cleanup;
    }

    //info("   # %s:%s (ID=%p) -- call rdma_resolve_addr\n", ep->cd.ei.host, ep->cd.ei.port, conn->id);
    rv = rdma_resolve_addr(conn->id, NULL, servinfo->ai_dst_addr, 2000);
    if (rv) {
        VERB_ERR("rdma_resolve_addr", rv);
        goto cleanup;
    }
    rv = 0;
    goto cleanup;
    
cleanup:    
    if (servinfo) {
        rdma_freeaddrinfo(servinfo);
    }
    return rv;    
}

static int 
ac_ibv_poll_ch(void *ch)
{
    int rv;
    struct rdma_cm_event *event = NULL;
    channel_t *channel = (channel_t*)ch;
    if (!channel) {
        return 0;
    }
    
    rv = rdma_get_cm_event(channel->ec, &event);
    if (rv) {
        return 0;
    }
    
    /* Receive event on this channel */
    struct rdma_cm_event event_copy;
    memcpy(&event_copy, event, sizeof(struct rdma_cm_event));
    rdma_ack_cm_event(event);
    
    switch (event_copy.event) {
    case RDMA_CM_EVENT_ADDR_RESOLVED:
    {
        //info_wtime("RDMA_CM_EVENT_ADDR_RESOLVED %p\n", event_copy.id);
        conn_t *conn = (conn_t*)event_copy.id->context;
        if (!conn) return 0;
        ep_t *ep = conn->conn_ctx.ep;
        if (!ep) return 0;
        rv = on_addr_resolved(event_copy.id);
        if (rv) {
            error("on_addr_resolved\n");
            /* Note: connection disconnected when calling terminate() */
            return 1;
        }
        /* Note: the QP's state is INIT */    
        break;
    }
    case RDMA_CM_EVENT_ROUTE_RESOLVED:
    {
        //info_wtime("RDMA_CM_EVENT_ROUTE_RESOLVED %p\n", event_copy.id);        
        /* Note: the QP's state is INIT */
        struct rdma_conn_param cm_params;
        memset(&cm_params, 0, sizeof(cm_params));
        /* rnr_retry: the total number of times that the QP will try 
         * to resend the packets when an RNR NACK was sent by the remote 
         * QP before reporting an error. The value 7 is special and specify 
         * to retry infinite times in case of RNR
         * => no IBV_WC_RNR_RETRY_EXC_ERR errors */
        cm_params.rnr_retry_count = 7;
        rv = rdma_connect(event_copy.id, &cm_params);
        if (rv) {
            VERB_ERR("rdma_connect", rv);
            /* Note: connection disconnected when calling terminate() */
            return 1;
        }
        break;
    }
    case RDMA_CM_EVENT_ADDR_ERROR:
    case RDMA_CM_EVENT_ROUTE_ERROR:
    {
        error("error while connecting -- %s; status: %d\n", 
            rdma_event_str(event_copy.event), event_copy.status);
        if (event_copy.id->context) {
            conn_t *conn = (conn_t*)event_copy.id->context;
            ep_t* ep = conn->conn_ctx.ep;
            /* Try to reconnect */
            rv = ac_handle_ep_error(ep);
            if (rv) {
                error("ac_handle_ep_error\n");
                return 1;
            }
        }
        break;
    }
    
    case RDMA_CM_EVENT_CONNECT_REQUEST:
    {
        /* New connection request -- no endpoint yet */
        info_wtime("Received connection requests (ID=%p)\n", event_copy.id);
//info("   # rnr_retry_count=%d\n", event_copy.param.conn.rnr_retry_count);
//info("   # retry_count=%d\n", event_copy.param.conn.retry_count);

        /* Note: new ID created (!= listen_id) */
        rv = on_connect_request(event_copy.id, channel->cd, 
                            &event_copy.param.conn);
        if (rv) {
            error("on_connect_request\n");
            /* Destroy connection since it cannot be referenced later */
            if (event_copy.id->context) 
                destroy_connection(event_copy.id->context);
            else 
                rdma_destroy_id(event_copy.id);
            return 1;
        }
        break;
    }
    case RDMA_CM_EVENT_ESTABLISHED:
    {
        /* Connection established */
        /* Note: the QP's state is RTS */
        conn_t *conn = (conn_t*)event_copy.id->context;
        if (!conn) {
            error("conn is NULL\n");
            return 1;
        }
        if (event_copy.id->ps == RDMA_PS_TCP) {
            channel->disconnects_left++;
        }
        info_wtime("New %s connection (ID=%p)\n", 
                (conn->conn_ctx.active ? "outgoing" : "incomming"), event_copy.id);
        /* Set the Minimum RNR NAK Timer */
        struct ibv_qp_attr attr;
        attr.min_rnr_timer = 1;
        rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_MIN_RNR_TIMER);
        if (rv) {
            VERB_ERR("ibv_query_qp", rv);
            return 1;
        }
#if 0
        struct ibv_qp_init_attr init_attr;
        rv = ibv_query_qp(conn->qp, &attr, 
                    IBV_QP_STATE | IBV_QP_MIN_RNR_TIMER |
                    IBV_QP_RNR_RETRY | IBV_QP_TIMEOUT |
                    IBV_QP_RETRY_CNT, 
                    &init_attr);
        if (rv) {
            VERB_ERR("ibv_query_qp", rv);
            return 1;
        }
        info("   # state = %s\n", qp_state_to_str(attr.qp_state));
        info("   # rnr_retry = %"PRIu8"\n", attr.rnr_retry);
        info("   # min_rnr_timer = %"PRIu8"\n", attr.min_rnr_timer);
        info("   # timeout = %"PRIu8"\n", attr.timeout);
        info("   # retry_cnt = %"PRIu8"\n", attr.retry_cnt);
#endif
        if (0 == conn->conn_ctx.active) {
            /* Incoming connection, e.g., predecessor */
            ep_t* ep = channel->cd->on_connection(conn);
            if (NULL == ep) {
                error("on_connection\n");
                return 1;
            }
            ep->cd.handle_data = channel->cd->handle_data;
            ep->cd.destroy_ep_data = channel->cd->destroy_ep_data;
            conn->conn_ctx.ep = ep;
        }
        else {
            /* Outgoing connection, e.g., successor */
            ep_t* ep = conn->conn_ctx.ep;
            if (NULL == ep->cd.on_connection(conn)) {
                error("on_connection\n");
                return 1;
            }
        }
        break;
    }
    case RDMA_CM_EVENT_DISCONNECTED:
    {
        /* Connection disconnected: This event is generated on both 
           sides of the connection in response to rdma_disconnect()*/
        channel->disconnects_left--;
        info("   # disconnecting ID=%p (still %d remain)\n", event_copy.id, channel->disconnects_left);
        if (event_copy.id->context) {
            conn_t *conn = (conn_t*)event_copy.id->context;
            if (!conn->init_disconnect) {
                /* Disconnection initiated remotely: tear-down connection */
                if (event_copy.id->verbs) 
                    rdma_disconnect(event_copy.id);
                /* and destroy endpoint */
                if (conn->conn_ctx.ep) {
                    ep_t* ep = conn->conn_ctx.ep;
                    ep->conn = NULL;    // do not call disconnect
                    ac_ep_destroy(ep);
                }
            }
            destroy_connection(conn);
        }
        else {
            rdma_destroy_id(event_copy.id);
        }
        break;
    }
    case RDMA_CM_EVENT_REJECTED:
    {
        /* Indicates that a connection request or response was rejected 
           by the remote end point. */        
        //info("RDMA_CM_EVENT_REJECTED: status=%d (ID=%p)\n",  event_copy.status, event_copy.id);
        conn_t *conn = (conn_t*)event_copy.id->context;
        ep_t* ep = conn->conn_ctx.ep;
        rv = ac_handle_ep_error(ep);
        if (rv) {
            error("ac_handle_ep_error\n");
            return 1;
        }
        break;
    }
    default:
        error("unexpected event -- %s; status: %d\n", 
            rdma_event_str(event_copy.event), event_copy.status);
        return 1;
    }
    return 0;
}

static int 
ac_ibv_poll_recv(ep_t *ep)
{
    int rv, ne;
    struct ibv_wc wc;    
    if (!ep) {
        return 0;
    }
    conn_t *conn = (conn_t*)ep->conn;

    if (conn->device.rcq == NULL) {
        error("cannot poll recv data\n");
        return 1;
    }
    
    ne = ibv_poll_cq(conn->device.rcq, 1, &wc);
    if (ne < 0) {
        VERB_ERR("ibv_poll_cq", rv);
        return 1;
    }
    if (0 == ne) {
        /* No data */
        return 0;
    }
    
    rv = handle_work_completion(conn, &wc);
    if (rv != WC_SUCCESS) {
        error("Completion with status 0x%x was found\n", wc.status);
        ac_ep_destroy(ep);
        return 0;
    }
#if 0    
info("recv [%p]: wr_id=%"PRIu64", byte_len=%"PRIu32"\n", ep, wc.wr_id, wc.byte_len);
//dump_bytes(conn->recv_mem[wc.wr_id].buf, wc.byte_len, "RECV_DATA");
#endif
    /* Received data into buffer conn->recv_mem[wc->wr_id].buf */
    ep->cd.handle_data(ep, conn->recv_mem[wc.wr_id].buf, wc.byte_len);
    /* Post another receive */
    rv = post_one_receive(conn, wc.wr_id);
    if (rv) {
        error("post_one_receive\n");
        return 1;
    }
}

static int 
ac_ibv_isend(ep_t *ep, shared_buf_t *sh_buf)
{
    uint32_t len = 0, avail;
    int ne, rv, i;
    reg_mem_t *mem = NULL;
    struct ibv_send_wr send_wr, *bad_send_wr = NULL;
    struct ibv_sge sge;
    send_buf_t *sb = NULL, *sb_iter;
    if (!ep) {
        error("ep is NULL\n");
        return 1;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        error("conn is NULL\n");
        return 1;
    }
    conn_ctx_t *send_ctx = &conn->conn_ctx;
    
    if (!sh_buf) {
        error("sh_buf is NULL\n");
        return 1;
    }

    if (!send_ctx->buffering) {
        /* No buffering */
        uint32_t avail_bytes = 
            (conn->device.scqe - send_ctx->outstanding_sends)*conn->sbuf_len;
        if (sh_buf->len > avail_bytes) {
            /* Cannot send message asynchronously -- drop it */
            info("Warning: Cannot send message asynchronously\n");
            return 0;
        }
    }

    uint8_t *buf = sh_buf->buf;
    uint32_t buf_len = sh_buf->len;
    while (send_ctx->outstanding_sends < conn->device.scqe) {
        /* Find available buffer / WR */
        for (i = 0; i < conn->device.scqe; i++) {
            if (conn->send_mem[i].avail)
                break;
        }
        mem = &conn->send_mem[i];
        memset(&send_wr, 0, sizeof(send_wr));
        send_wr.wr_id = i; 
        send_wr.opcode = IBV_WR_SEND;
        send_wr.sg_list = &sge;
        send_wr.send_flags = IBV_SEND_SIGNALED;
        send_wr.num_sge = 1;
        if (buf_len < conn->device.max_inline_data) {
            /* Send inline -- no need of registered buffers */
            len = buf_len;
            send_wr.send_flags |= IBV_SEND_INLINE;
            sge.addr = (uintptr_t)buf;
        }
        else {
            len = buf_len > conn->sbuf_len ? conn->sbuf_len : buf_len;
            memcpy(mem->buf, buf, len);
            sge.addr = (uintptr_t)mem->buf;
            sge.lkey = mem->mr->lkey;
        }
        sge.length = len;
        
HRT_TIMESTAMP_T t1,t2;
uint64_t ticks;
HRT_GET_TIMESTAMP(t1);
        rv = ibv_post_send(conn->qp, &send_wr, &bad_send_wr);
        if (rv) {
            VERB_ERR("ibv_post_send", rv);
            return 1;
        }
HRT_GET_TIMESTAMP(t2);
HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        send_ctx->outstanding_sends++;
//info_wtime("[ID=%p] Post send op (%"PRIu32" bytes) -- WR=%d; outstanding_sends=%d; time=%lf usecs\n", conn->id, len, i, send_ctx->outstanding_sends, HRT_GET_USEC(ticks));
        mem->avail = 0;
        buf_len -= len;
        if (!buf_len) {
            /* Send entire buffer */
            break;
        }
        buf += len;
    }

    if (buf_len) {
        /* Add shared buffer to the list of sending buffers */
        sb = (send_buf_t*)malloc(sizeof(send_buf_t));
        if (NULL == sb) {
            error("malloc (%s)\n", strerror(errno));
            return 1;
        }
        memset(sb, 0, sizeof(send_buf_t));
        sb->sh_buf = sh_buf;
        sb->bytes_sent = sh_buf->len - buf_len;
        ac_ibv_mod.bytes_to_send += sh_buf->len - sb->bytes_sent;
        sh_buf->shared_count++;
        //info("### buffering %"PRIu32" bytes -- bytes_to_send=%"PRIu64"\n", buf_len, ac_ibv_mod.bytes_to_send);
    
        /* Add buffer at the end of the list */
        sb->next = NULL;
        if (NULL == send_ctx->send_buf) {
            sb->prev = NULL;
            send_ctx->send_buf = sb;
        }
        else {
            sb_iter = send_ctx->send_buf;
            while(sb_iter->next != NULL) {
                sb_iter = sb_iter->next;
            }
            sb_iter->next = sb;
            sb->prev = sb_iter;
        }
    }

    return 0;    
}

static int 
ac_ibv_poll_send(ep_t *ep)
{
    struct ibv_wc wc;
    int ne, rv;
    if (!ep) {
        error("ep is NULL\n");
        return -1;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        error("conn is NULL\n");
        return -1;
    }
    conn_ctx_t *send_ctx = &conn->conn_ctx;
    
    if (!send_ctx->outstanding_sends) {
        return 0;
    }
     
    ne = ibv_poll_cq(conn->device.scq, 1, &wc);
    if (ne < 0) {
        VERB_ERR("ibv_poll_cq", ne);
        return -1;
    }
    if (!ne) {
        /* Send not completed */
        return send_ctx->outstanding_sends;
    }
    send_ctx->outstanding_sends--;
    conn->send_mem[wc.wr_id].avail = 1;
//info_wtime("[ID=%p] Send op completed -- WR=%d, outstanding_sends=%d\n", conn->id, wc.wr_id, send_ctx->outstanding_sends);
       
    rv = handle_work_completion(conn, &wc);
    if ((rv == WC_SOFTWARE_BUG) || (rv == WC_ERROR)) {
        error("Completion with status 0x%x was found\n", wc.status);
        ac_net_mod->terminate(1);
    }
    else if (rv == WC_FAILURE) {
        error("Completion with status 0x%x was found\n", wc.status);
/* Note: In order to reuse a QP, it can be transitioned to Reset 
 * state from any state by calling to ibv_modify_qp(). If prior to 
 * this state transition, there were any Work Requests or completions 
 * in the send or receive queues of that QP, they will be cleared 
 * from the queues. */
        ac_ep_destroy(ep);
        return send_ctx->outstanding_sends;
    }
    if (!send_ctx->buffering) {
        return send_ctx->outstanding_sends;
    }

    struct ibv_send_wr send_wr, *bad_send_wr = NULL;
    struct ibv_sge sge;
    send_buf_t *sb, *next;
    reg_mem_t *mem = &conn->send_mem[wc.wr_id];
    uint8_t *buf = mem->buf;
    uint32_t total_len = 0, len;

    sb = send_ctx->send_buf;
    while (sb != NULL) {
        len = sb->sh_buf->len - sb->bytes_sent;
        if (0 == len) {
            /* Done with this buffer */
            sb->sh_buf->shared_count--;
            /* Remove send buffer from the list ... */
            next = sb->next;
            if (NULL != sb->prev) {
                sb->prev->next = sb->next;
            }
            if (NULL != sb->next) {
                sb->next->prev = sb->prev;
            }
            if (sb == send_ctx->send_buf) {
                send_ctx->send_buf = sb->next;
            }
            if (0 == sb->sh_buf->shared_count) {
                /* free shared buffer */
                if (NULL != sb->sh_buf) {
                    free(sb->sh_buf);
                }
            }
            free(sb);
            sb = next;
            continue;
        }
        if (len > conn->sbuf_len - total_len) 
            len = conn->sbuf_len - total_len;
        memcpy(buf, sb->sh_buf->buf+sb->bytes_sent, len);
        buf += len;
        total_len += len;
        sb->bytes_sent += len;
        ac_ibv_mod.bytes_to_send -= len;
        if (total_len >= conn->sbuf_len) {
            /* Registered buffer is full */
            break;
        }
    }
    if (!total_len) return send_ctx->outstanding_sends;

    mem->avail = 0;
    memset(&send_wr, 0, sizeof(send_wr));
    send_wr.wr_id = wc.wr_id; 
    send_wr.opcode = IBV_WR_SEND;
    send_wr.sg_list = &sge;
    send_wr.send_flags = IBV_SEND_SIGNALED;
    send_wr.num_sge = 1;
    if (total_len < conn->device.max_inline_data) {
        /* Send inline -- no need of registered buffers */
        send_wr.send_flags |= IBV_SEND_INLINE;
    }
    sge.addr = (uintptr_t)mem->buf;
    sge.length = total_len;
    sge.lkey = mem->mr->lkey;
    rv = ibv_post_send(conn->qp, &send_wr, &bad_send_wr);
    if (rv) {
        VERB_ERR("ibv_post_send", rv);
        return -1;
    }
    send_ctx->outstanding_sends++;
//info("[ID=%p] Post send op (%"PRIu32" bytes) -- WR=%d; bytes_to_send=%"PRIu64"; outstanding_sends=%d\n", conn->id, total_len, wc.wr_id, ac_ibv_mod.bytes_to_send, send_ctx->outstanding_sends);

    return send_ctx->outstanding_sends;
}

static int 
ac_ibv_done_sending(ep_t *ep)
{
    struct ibv_wc wc;
    int ne, rv;
    if (!ep) {
        return 1;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        return 1;
    }
    conn_ctx_t *send_ctx = &conn->conn_ctx;
//info("[ID=%p] outstanding_sends=%d\n", conn->id, send_ctx->outstanding_sends);
    
    return (send_ctx->outstanding_sends == 0);
}

static int 
ac_ibv_ongoing_bytes(ep_t *ep)
{
    struct ibv_wc wc;
    int ne, rv;
    if (!ep) {
        return 0;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        return 0;
    }
    conn_ctx_t *send_ctx = &conn->conn_ctx;
    
    return send_ctx->outstanding_sends;
}


static void*
ac_ibv_create_ch()
{
 
#if 0   
    int num_devs, i, rv;
    struct ibv_device **ib_devs = NULL;
    
        ib_devs = ibv_get_device_list(&num_devs);
        if (NULL == ib_devs) {
            error("ibv_get_device_list: %d (%s)\n", errno, strerror(errno));
            return NULL;
        }
        if (0 == num_devs) {
            error("No HCAs available\n");
            return NULL;
        }
        ibv_free_device_list(ib_devs);
        info("# new device context\n");
#endif

    channel_t *channel = NULL;
    channel = (channel_t*)malloc(sizeof(channel_t));
    if (!channel) {
        error("malloc\n");
        return NULL;
    }

    memset(channel, 0, sizeof(channel_t));
    channel->ec = rdma_create_event_channel();
    if (NULL == channel->ec) {
        error("rdma_create_event_channel: %d (%s)\n", errno, strerror(errno));
        free(channel);
        return NULL;
    } 
    if (0 != set_blocking(channel->ec->fd, 0)) {
        error("set_blocking\n");
        rdma_destroy_event_channel(channel->ec);
        free(channel);
        return NULL;
    } 
    return channel;
}

static void
ac_ibv_destroy_ch(void *ch)
{
    channel_t *channel = (channel_t*)ch;
    if (!channel) return;
    if (channel->id) {
        rdma_destroy_id(channel->id);
        channel->id = NULL;
    }
    if (channel->ec) {
        rdma_destroy_event_channel(channel->ec);
        channel->ec = NULL;
    }
    if (channel->cd) {
        free(channel->cd);
        channel->cd = NULL;
    }
    free(channel);
}

static void 
ac_ibv_wait_for_disconnects(void *ch)
{
    int rv;
    channel_t *channel = (channel_t*)ch;
    if (!channel) {
        info("   no connections\n");
        return;
    }
    info("   #connections: %d\n", channel->disconnects_left);

    while (channel->disconnects_left) {
		rv = ac_ibv_poll_ch(ch);
		if (rv) {
			error("ac_ibv_poll_ch\n");
            ac_net_mod->terminate(1);
		}
	}
}

/* ================================================================== */
/* Unreliable datagrams */
static int
ac_ibv_ud_setup(ud_t* ud)
{
    int rv, i;
    conn_t *conn = NULL;
    struct ibv_qp_init_attr init_attr;
    struct ibv_qp_attr attr;
    struct ibv_port_attr port_attr;
    
    if (!ud) {
        error("ud is NULL\n");
        return 1;
    }
    if (ud->conn) {
        error("existing conn\n");
        return 1;
    }
    
    /* Create connection */
    ud->conn = conn = (conn_t*)malloc(sizeof(conn_t));
    if (!ud->conn) {
        error("malloc\n");
        return 1;
    }
    memset(conn, 0, sizeof(conn_t));
    
    rv = init_device(&conn->device, ud->cd.scount, ud->cd.rcount);
    if (rv) {
        error("init_device\n");
        return 1;
    }

    /* Create QP */
    memset(&init_attr, 0, sizeof init_attr);
    init_attr.send_cq = conn->device.scq;
    init_attr.recv_cq = conn->device.rcq;
    init_attr.qp_type = IBV_QPT_UD;
    init_attr.cap.max_send_wr = conn->device.scqe;
    init_attr.cap.max_recv_wr = conn->device.rcqe;
    init_attr.cap.max_send_sge = 1;
    init_attr.cap.max_recv_sge = 1;
    init_attr.cap.max_inline_data = conn->device.max_inline_data;
    conn->qp = ibv_create_qp(conn->device.pd, &init_attr); 
    if (NULL == conn->qp) {
        error("ibv_create_qp\n");
        return 1;
    }
    
    /* Move the UD QP into the INIT state */
    memset(&attr, 0, sizeof(attr));
    attr.qp_state   = IBV_QPS_INIT;
    attr.pkey_index = conn->device.pkey_index;
    attr.port_num   = conn->device.port_num;
    attr.qkey       = 0;
    rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_STATE | IBV_QP_PKEY_INDEX
                       | IBV_QP_PORT | IBV_QP_QKEY); 
    if (rv) {
        VERB_ERR("ibv_modify_qp", rv);
        return 1;
    }
    
    /* Move the UD QP to RTR */
    attr.qp_state = IBV_QPS_RTR;
    rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_STATE); 
    if (rv) {
        VERB_ERR("ibv_modify_qp", rv);
        return 1;
    }

    /* Move the UD QP to RTS */
    memset(&attr, 0, sizeof(attr));
    attr.qp_state = IBV_QPS_RTS;
    attr.sq_psn = 0;
    rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_STATE | IBV_QP_SQ_PSN); 
    if (rv) {
        VERB_ERR("ibv_modify_qp", rv);
        return 1;
    }
#if 0
    rv = ibv_query_qp(conn->qp, &attr, IBV_QP_STATE, &init_attr);
    if (rv) {
        VERB_ERR("ibv_query_qp", rv);
        return 1;
    }
    info("   #state = %s\n", qp_state_to_str(attr.qp_state));
#endif       
    
    /* Set buffers length */
    set_buffer_len(conn, &ud->cd, 1);

    /* Register memory */
    if (register_memory(conn, 1)) {
        return 1;
    }
    
    /* Post receives */
    if (post_receives(conn)) {
        return 1;
    }
    
    ud->ud_info.len = sizeof(ud_ep_t);
    ud->ud_info.endpoint = malloc(ud->ud_info.len);
    if (!ud->ud_info.endpoint) {
        error("malloc\n");
        return 1;
    }
    memset(ud->ud_info.endpoint, 0, ud->ud_info.len);
    ud_ep_t *ud_ep = (ud_ep_t*)ud->ud_info.endpoint;
    ud_ep->qpn = conn->qp->qp_num;
    ud_ep->lid = conn->device.lid;
    
    info_wtime("Listening for datagrams on lid=%"PRIu16"; qpn=%"PRIu32"\n", 
                    conn->device.lid, conn->qp->qp_num);
    
    return 0; 
}

/**
 * Sending UD data
 */
static int 
ac_ibv_sendto(ud_t* ud, void *endpoint, void *buf, uint32_t buf_len)
{
    int i, rv;
    struct ibv_send_wr send_wr, *bad_send_wr = NULL;
    struct ibv_sge sge;
    struct ibv_ah_attr ah_attr;

    if (!ud) {
        error("ud is NULL\n");
        return 1;
    }
    ud_ep_t *ud_ep = (ud_ep_t*)endpoint;
    if (!endpoint) {
        error("endpoint is NULL\n");
        return 1;
    }
    if (!buf) {
        error("buf is NULL\n");
        return 1;
    }
    conn_t *conn = (conn_t*)ud->conn;
    if (!conn) {
        error("conn is NULL\n");
        return 1;
    }
    
    if ((buf_len == 0) || (buf_len > conn->device.mtu)) {
        error("UD message too long: %"PRIu32" not in [1,%"PRIu32"]\n", 
                    buf_len, conn->device.mtu);
        return 1;
    }
    
    /* Find available buffer / WR */
    for (i = 0; i < conn->device.scqe; i++) {
        if (conn->send_mem[i].avail) break;
    }
    if (i == conn->device.scqe) {
        /* Cannot send -- just drop it */
        info("Cannot send datagram\n");
        return 0;
    }
    conn->send_mem[i].avail = 0;
    
    memset(&send_wr, 0, sizeof(send_wr));
    send_wr.wr_id = i;
    send_wr.opcode = IBV_WR_SEND;
    send_wr.sg_list = &sge;
    send_wr.num_sge = 1;
    send_wr.send_flags = IBV_SEND_SIGNALED;

    memset(&ah_attr, 0, sizeof ah_attr);
    ah_attr.dlid = ud_ep->lid;
    ah_attr.port_num = conn->device.port_num;
    conn->send_mem[i].ah = ibv_create_ah(conn->device.pd, &ah_attr);
    if (!conn->send_mem[i].ah) {
        error("ibv_create_ah\n");
        return 1;
    }
    send_wr.wr.ud.ah = conn->send_mem[i].ah;

    send_wr.wr.ud.remote_qpn  = ud_ep->qpn;
    send_wr.wr.ud.remote_qkey = 0;
    if (buf_len < conn->device.max_inline_data) {
        /* Send inline -- no need of registered buffers */
        send_wr.send_flags |= IBV_SEND_INLINE;
        sge.addr = (uintptr_t)buf;
    }
    else {
        /* Copy data to registered buffers */
        memcpy(conn->send_mem[i].buf, buf, buf_len);
        sge.addr = (uintptr_t)conn->send_mem[i].buf;
        sge.lkey = conn->send_mem[i].mr->lkey;
    }
    sge.length = buf_len;
    rv = ibv_post_send(conn->qp, &send_wr, &bad_send_wr);
    if (rv) {
        VERB_ERR("ibv_post_send", rv);
        return 1;
    }
    conn->conn_ctx.outstanding_sends++;

    return 0;
}

static int 
ac_ibv_poll_sendto(ud_t* ud)
{
    struct ibv_wc wc;
    int ne, rv;
    struct ibv_send_wr send_wr, *bad_send_wr = NULL;
    struct ibv_sge sge;
    if (!ud) {
        error("ep is NULL\n");
        return 1;
    }
    conn_t *conn = (conn_t*)ud->conn;
    if (!conn) {
        error("conn is NULL\n");
        return 1;
    }
    
    if (!conn->conn_ctx.outstanding_sends) {
        return 0;
    }
     
    while (1) {
        ne = ibv_poll_cq(conn->device.scq, 1, &wc);
        if (ne < 0) {
            VERB_ERR("ibv_poll_cq", ne);
            return 1;
        }
        if (!ne) {
            /* No work completion */
            break;
        }
        conn->conn_ctx.outstanding_sends--;
        conn->send_mem[wc.wr_id].avail = 1;
        rv = ibv_destroy_ah(conn->send_mem[wc.wr_id].ah);
        if (rv) {
            VERB_ERR("ibv_destroy_ah", rv);
            return 1;
        }
        conn->send_mem[wc.wr_id].ah = NULL;
        
        rv = handle_work_completion(conn, &wc);
        if (rv != WC_SUCCESS) {
            error("Completion with status 0x%x was found\n", wc.status);
            return 1;
        }
    }
    return 0;
}

static int 
ac_ibv_ud_poll_recv(ud_t *ud)
{
    int rv, ne;
    struct ibv_wc wc;
    ud_ep_t ud_ep;

    if (!ud) {
        return 0;
    }
    conn_t *conn = (conn_t*)ud->conn;
    if (!conn) {
        error("conn is NULL\n");
        return 1;
    }
        
    ne = ibv_poll_cq(conn->device.rcq, 1, &wc);
    if (ne < 0) {
        VERB_ERR("ibv_poll_cq", rv);
        return 1;
    }
    if (0 == ne) {
        /* No data */
        return 0;
    }

    rv = handle_work_completion(conn, &wc);
    if (rv != WC_SUCCESS) {
        error("Completion with status 0x%x was found\n", wc.status);
        return 1;
    }
    ud_ep.qpn = wc.src_qp;
    ud_ep.lid = wc.slid;

    /* Received data into buffer conn->recv_mem[wc->wr_id].buf */
    ud->cd.handle_data(&ud_ep, 
            conn->recv_mem[wc.wr_id].buf + sizeof(struct ibv_grh), 
            wc.byte_len - sizeof(struct ibv_grh));

    /* Post another receive */
    rv = post_one_receive(conn, wc.wr_id);
    if (rv) {
        error("post_one_receive\n");
        return 1;
    }
}

static int 
ac_ibv_cmp_ud_eps(void *left, void *right)
{
    ud_ep_t *ud_ep_left = (ud_ep_t*)left;
    ud_ep_t *ud_ep_right = (ud_ep_t*)right;
    
    if (ud_ep_left->qpn != ud_ep_right->qpn) {
        return 1;
    }
    if (ud_ep_left->lid != ud_ep_right->lid) {
        return 1;
    }
    return 0;
}

static int 
ac_ibv_cp_ud_ep(void **dest, void *src)
{
    *dest = malloc(sizeof(ud_ep_t));
    if (NULL == *dest) {
        error("malloc\n");
        return 1;
    }
    memcpy(*dest, src, sizeof(ud_ep_t));
    return 0;
}

static char*
ac_ibv_ud_ep_to_str(char *str, uint32_t len, void *endpoint)
{
    ud_ep_t *ud_ep = (ud_ep_t*)endpoint;
    if (!endpoint) return "";
    if (len < 64) return "";
    
    sprintf(str, "lid=%"PRIu16"; qpn=%"PRIu32, 
            ud_ep->lid,
            ud_ep->qpn);
    return str;
}

static void
ac_ibv_print_ud_ep(void *endpoint)
{
    ud_ep_t *ud_ep = (ud_ep_t*)endpoint;
    if (!endpoint) return;
    
    info("lid: %"PRIu16"; qp_num: %"PRIu32, 
            ud_ep->lid,
            ud_ep->qpn);
}

/* ================================================================== */
/* Others */
static int
init_device(device_t *dev, int scqe, int rcqe)
{
    int num_devs, i, rv;
    struct ibv_device **ib_devs = NULL;
    
    if (NULL == dev->context) {
        ib_devs = ibv_get_device_list(&num_devs);
        if (0 == num_devs) {
            error("No HCAs available\n");
            return 1;
        }
        if (NULL == ib_devs) {
            error("ibv_get_device_list\n");
            return 1;
        }
        
        for (i = 0; i < num_devs; i++) {
            dev->context = ibv_open_device(ib_devs[0]);
            if (dev->context) break;
        }
        ibv_free_device_list(ib_devs);
        
        if (NULL == dev->context) {
            /* Cannot find device */
            error("Cannot find device\n");
            return 1;
        }
    }
    
    /* Get device's attributes */
    if(ibv_query_device(dev->context, &dev->dev_attr)){
        error("ibv_query_device");
        return 1;
    }
    
    /* Find port */
    if (!dev->port_num) {
        struct ibv_port_attr port_attr;
        for (i = 1; i <= dev->dev_attr.phys_port_cnt; i++) {
            rv = ibv_query_port(dev->context, i, &port_attr);
            if (rv) {
                VERB_ERR("ibv_query_port", rv);
                return 1;
            }
            if (IBV_PORT_ACTIVE != port_attr.state) {
                continue;
            }
            
            /* find index of pkey 0xFFFF */
            uint16_t pkey, j;
            for (j = 0; j < dev->dev_attr.max_pkeys; j++) {
                if (ibv_query_pkey(dev->context, i, j, &pkey)) {
                    VERB_ERR("ibv_query_pkey", rv);
                    return 1;
                }
                pkey = ntohs(pkey);// & IB_PKEY_MASK;
                //info("# pkey_value = %"PRIu16" for index %"PRIu16"\n", pkey, j);
                if (pkey == 0xFFFF) {
                    dev->pkey_index = j;
                    break;
                }
            }
            
            /* Found port */
            dev->port_num = i;
            dev->mtu = 1 << (port_attr.active_mtu + 7);
            dev->lid = port_attr.lid;
            break;
        }
        if (!dev->port_num) {
            error("Cannot find port\n");
            return 1;
        }
    }
    
    /* Find out if this device supports RC QPs */
    if(test_qp_support_rc(dev->context)) {
        error("test_qp_support_rc");
        return 1;
    }
    
    /* Allocate the UD protection domain */
    dev->pd = ibv_alloc_pd(dev->context);
    if (!dev->pd) {
        error("ibv_alloc_pd");
        return 1;
    }
    
    /* Find max inlinre */
    rv = find_max_inline(dev->context, dev->pd, &dev->max_inline_data);
    if (rv) {
        error("Cannot find max inline data\n");
        return 1;
    }
    //info("# max_inline=%"PRIu32" bytes\n", dev->max_inline_data);    
    
    /* Create completion queues */
    if (!scqe && !rcqe) {
        error("No completion queues\n");
        return 1;
    }
    dev->scqe = scqe;
    dev->rcqe = rcqe;
    if (dev->scqe) {
        dev->scq = ibv_create_cq(dev->context, dev->scqe, NULL, NULL, 0);
        if (!dev->scq) {
            error("ibv_create_cq");
            return 1;
        }
    }
    if (dev->rcqe) {
        dev->rcq = ibv_create_cq(dev->context, dev->rcqe, NULL, NULL, 0);
        if (!dev->rcq) {
            error("ibv_create_cq");
            return 1;
        }
    }
    if (!dev->scq) dev->scq = dev->rcq;
    if (!dev->rcq) dev->rcq = dev->scq;
    
    return 0;
}

static int
test_qp_support_rc(struct ibv_context *device_context)
{
    int rc;
    struct ibv_pd *pd = NULL;
    struct ibv_cq *cq = NULL; 
    struct ibv_qp_init_attr qpia;
    struct ibv_qp *qp = NULL;
    
    /* Try to make both the PD and CQ */
    pd = ibv_alloc_pd(device_context);
    if (NULL == pd) {
        return 1;
    }
    
    cq = ibv_create_cq(device_context, 2, NULL, NULL, 0);
    if (NULL == cq) {
        rc = 1;
        goto out;
    }

    /* Create QP of type IBV_QPT_RC */
    memset(&qpia, 0, sizeof(qpia));
    qpia.qp_context = NULL;
    qpia.send_cq = cq;
    qpia.recv_cq = cq;
    qpia.srq = NULL;
    qpia.cap.max_send_wr = 1;
    qpia.cap.max_recv_wr = 1;
    qpia.cap.max_send_sge = 1;
    qpia.cap.max_recv_sge = 1;
    qpia.cap.max_inline_data = 0;
    qpia.qp_type = IBV_QPT_RC;
    qpia.sq_sig_all = 0;
    
    qp = ibv_create_qp(pd, &qpia);
    if (NULL == qp) {
        rc = 1;
        goto out;
    }
    
    ibv_destroy_qp(qp);
    rc = 0;
 
out:
    /* Free the PD and/or CQ */
    if (NULL != pd) {
        ibv_dealloc_pd(pd);
    }
    if (NULL != cq) {
        ibv_destroy_cq(cq);
    }

    return rc;   
}

static int 
on_connect_request(struct rdma_cm_id *id, 
                   conn_data_t *cd, 
                   struct rdma_conn_param *cm_params) 
{
    int rv;
    struct ibv_qp_init_attr qp_attr;
    struct ibv_port_attr port_attr;
    conn_t *conn = NULL;
    device_t *device = NULL;

    if (id->context) {
        conn = (conn_t*)id->context;
    }
    else {
        id->context = conn = (conn_t*)malloc(sizeof(conn_t));
        if (!conn) {
            error("malloc\n");
            return 1;
        }
        memset(conn, 0, sizeof(conn_t));
        conn->id = id;
        //info("# new connection\n");
    }

    if (NULL == conn->device.rcq) {
        conn->device.context = id->verbs;
        rv = init_device(&conn->device, cd->scount, cd->rcount);
        if (rv) {
            error("init_device");
            return 1;
        }
    }
    
    /* Passive side */
    conn->conn_ctx.active = 0;

    /* Create QP */
    memset(&qp_attr, 0, sizeof qp_attr);
    qp_attr.send_cq = conn->device.scq;
    qp_attr.recv_cq = conn->device.rcq;
    qp_attr.qp_type = IBV_QPT_RC;
    qp_attr.cap.max_send_wr = conn->device.scqe;
    qp_attr.cap.max_recv_wr = conn->device.rcqe;
    qp_attr.cap.max_send_sge = (conn->device.scqe ? 1 : 0);
    qp_attr.cap.max_recv_sge = (conn->device.rcqe ? 1 : 0);
    qp_attr.cap.max_inline_data = conn->device.max_inline_data;
    rv = rdma_create_qp(conn->id, conn->device.pd, &qp_attr);
    if (rv) {
        VERB_ERR("rdma_create_qp", rv);
        return 1;
    }
    conn->qp = id->qp;
    
    /* Set buffers length */
    set_buffer_len(conn, cd, 0);

    /* Register memory */
    if (register_memory(conn, 0)) {
        return 1;
    }
    
    /* Post receives */
    if (post_receives(conn)) {
        return 1;
    }

    //info("calling rdma_accept(ID=%p)\n", id);
    rv = rdma_accept(id, cm_params);
    if (-1 == rv) {
        VERB_ERR("rdma_accept", rv);
        return 1; 
    }

    return 0;
}

static int 
on_addr_resolved(struct rdma_cm_id *id)
{
    int rv;
    struct ibv_qp_init_attr qp_attr;
    struct ibv_port_attr port_attr;
    conn_t *conn = (conn_t*)id->context;
    if (!conn) {
        error("conn is NULL\n");
        return 1;
    }
    ep_t *ep = conn->conn_ctx.ep;
    if (!ep) {
        error("ep is NULL\n");
        return 1;
    }
    
    if (NULL == conn->device.rcq) {
        conn->device.context = id->verbs;
        rv = init_device(&conn->device, ep->cd.scount, ep->cd.rcount);
        if (rv) {
            error("init_device");
            return 1;
        }
        rv = ibv_query_port(id->verbs, id->port_num, &port_attr);
        if (rv) {
            VERB_ERR("ibv_query_port", rv);
            return 1;
        }
        conn->device.mtu = 1 << (port_attr.active_mtu + 7);
        //info("# mtu = %"PRIu32"\n", conn->device.mtu);        
        conn->device.lid = port_attr.lid;
    }
        
    /* Create QP */
    memset(&qp_attr, 0, sizeof qp_attr);
    qp_attr.send_cq = conn->device.scq;
    qp_attr.recv_cq = conn->device.rcq;
    qp_attr.qp_type = IBV_QPT_RC;
    qp_attr.cap.max_send_wr = conn->device.scqe;
    qp_attr.cap.max_recv_wr = conn->device.rcqe;
    qp_attr.cap.max_send_sge = (conn->device.scqe ? 2 : 0);
    qp_attr.cap.max_recv_sge = (conn->device.rcqe ? 2 : 0);
    qp_attr.cap.max_inline_data = conn->device.max_inline_data;
    rv = rdma_create_qp(id, conn->device.pd, &qp_attr);
    if (rv) {
        VERB_ERR("rdma_create_qp", rv);
        return 1;
    }
    conn->qp = id->qp;
    
    /* Set buffers length */
    set_buffer_len(conn, &ep->cd, 0);
    /* Register memory */
    if (register_memory(conn, 0)) {
        return 1;
    }
    
    /* Post receives */
    if (post_receives(conn)) {
        return 1;
    }
    
    rv = rdma_resolve_route(id, TIMEOUT_IN_MS);
    if (rv) {
        VERB_ERR("rdma_resolve_route", rv);
        return 1; 
    }

    return 0;
}

static void 
set_buffer_len(conn_t *conn, conn_data_t *cd, int is_ud)
{
    if (cd->scount) {
        conn->sbuf_len = cd->sbuf_len;
        if (conn->sbuf_len == 0) {
            conn->sbuf_len = conn->device.mtu;
        }
        else if (!is_ud) {
            if (conn->sbuf_len > RC_SEND_MAX_LEN) {
                conn->sbuf_len = RC_SEND_MAX_LEN;
            }
            if (conn->sbuf_len > conn->device.dev_attr.max_mr_size) {
                conn->sbuf_len = conn->device.dev_attr.max_mr_size;
            }
        }
    }
    else {
        conn->sbuf_len = 0;
    }
    
    if (cd->rcount) {
        conn->rbuf_len = cd->rbuf_len;
        if (conn->rbuf_len == 0) {
            conn->rbuf_len = conn->device.mtu;
        }
        else if (!is_ud) {
            if (conn->rbuf_len > RC_SEND_MAX_LEN) {
                conn->rbuf_len = RC_SEND_MAX_LEN;
            }
            if (conn->rbuf_len > conn->device.dev_attr.max_mr_size) {
                conn->rbuf_len = conn->device.dev_attr.max_mr_size;
            }
        }
    }
    else {
        conn->rbuf_len = 0;
    }
}

static int
register_memory(conn_t *conn, int is_ud)
{   
    int i;
    uint32_t grh_len = 0;
    
    if (is_ud) {
        grh_len = sizeof(struct ibv_grh);
        /* No need to send buffers; all UD data is inline */
        //goto receive_buffers;
    }
    
    /* Register memory for receive buffers */
    if ((0 == conn->sbuf_len) || 
        (0 == conn->device.scqe) || 
        (conn->send_mem)) 
    {
        goto receive_buffers;
    }
    conn->send_mem = (reg_mem_t*)
                    malloc(conn->device.scqe * sizeof(reg_mem_t));
    if (NULL == conn->send_mem) {
        error("malloc");
        return 1;
    }
    memset(conn->send_mem, 0, conn->device.scqe * sizeof(reg_mem_t));
    for (i = 0; i < conn->device.scqe; i++) {
        /* Allocate buffer */        
        conn->send_mem[i].buf = malloc(conn->sbuf_len);
        if (NULL == conn->send_mem[i].buf) {
            error("malloc");
            return 1;
        }
        memset(conn->send_mem[i].buf, 0, conn->sbuf_len);
        /* Set length */
        conn->send_mem[i].len = conn->sbuf_len;
        /* Mark as available */
        conn->send_mem[i].avail = 1;
        /* Register memory */
        conn->send_mem[i].mr = ibv_reg_mr(conn->device.pd, 
                    conn->send_mem[i].buf, conn->send_mem[i].len,
                    IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE);
        if (NULL == conn->send_mem[i].mr) {
            error("ibv_reg_mr");
            return 1;
        }
    }
    
receive_buffers:    
    /* Register memory for receive buffers */
    if ((0 == conn->rbuf_len) || 
        (0 == conn->device.rcqe) || 
        (conn->recv_mem)) 
    {
        return 0;
    }
    conn->recv_mem = (reg_mem_t*)
                    malloc(conn->device.rcqe * sizeof(reg_mem_t));
    if (NULL == conn->recv_mem) {
        error("malloc");
        return 1;
    }
    memset(conn->recv_mem, 0, conn->device.rcqe * sizeof(reg_mem_t));
    for (i = 0; i < conn->device.rcqe; i++) {
        /* Set length */
        conn->recv_mem[i].len = conn->rbuf_len + grh_len;
        /* Allocate buffer */        
        conn->recv_mem[i].buf = malloc(conn->recv_mem[i].len);
        if (NULL == conn->recv_mem[i].buf) {
            error("malloc");
            return 1;
        }
        memset(conn->recv_mem[i].buf, 0, conn->recv_mem[i].len);
        /* Register memory */
        conn->recv_mem[i].mr = ibv_reg_mr(conn->device.pd, 
                    conn->recv_mem[i].buf, conn->recv_mem[i].len,
                    IBV_ACCESS_LOCAL_WRITE | IBV_ACCESS_REMOTE_WRITE);
        if (NULL == conn->recv_mem[i].mr) {
            error("ibv_reg_mr");
            return 1;
        }
    }
    
    return 0;
}

static void 
deregister_memory(conn_t *conn)
{
    int i;
    int rv;
    
    /* Deregister memory for receive buffers */
    if (conn->recv_mem) {
        for (i = 0; i < conn->device.rcqe; i++) {
            if (conn->recv_mem[i].mr) {
                rv = ibv_dereg_mr(conn->recv_mem[i].mr);
                if (0 != rv) {
                    VERB_ERR("ibv_dereg_mr", rv);
                }
            }
            if (conn->recv_mem[i].buf) {
                free(conn->recv_mem[i].buf);
            }
        }
        free(conn->recv_mem);
        conn->recv_mem = NULL;
    }
    
    /* Deregister memory for send buffers */
    if (conn->send_mem) {
        for (i = 0; i < conn->device.scqe; i++) {
            if (conn->send_mem[i].ah) {
                rv = ibv_destroy_ah(conn->send_mem[i].ah);
                if (rv) {
                    VERB_ERR("ibv_destroy_ah", rv);
                }
            }
            if (conn->send_mem[i].mr) {
                rv = ibv_dereg_mr(conn->send_mem[i].mr);
                if (0 != rv) {
                    VERB_ERR("ibv_dereg_mr", rv);
                }
            }
            if (conn->send_mem[i].buf) {
                free(conn->send_mem[i].buf);
            }
        }
        free(conn->send_mem);
        conn->send_mem = NULL;
    }
}

/* 
 * On Receive Requests (source: rdmamojo.com)
 * 
 * The Receive Request is working in resolution of messages 
 * and not in resolution of bytes.
 *
 * Every Receive Request will handle only one incoming message:
 * for each incoming message one Receive Request will be fetched 
 * from the head of the Receive Queue. The messages will be handled 
 * by the order of their arrival.
 *
 * In your example there are 2 Receive Requests that each has n bytes:
 *   - Receiving a message of n bytes or less, is fine
 *   - Receiving a message with more than n bytes will cause an error 
 *   (since there isn't enough room to hold the message)
 */
static int
post_receives(conn_t *conn)
{
    int i;
    int rv;
    struct ibv_recv_wr *bad_wr = NULL;
    struct ibv_recv_wr *wr_array = NULL;
    struct ibv_sge *sg_array = NULL;

    if ((conn->rbuf_len == 0) || (conn->device.rcqe == 0)) {
        return 0;
    }
    
    wr_array = (struct ibv_recv_wr*)
                        malloc(conn->device.rcqe*sizeof(struct ibv_recv_wr));
    if (!wr_array) {
        error("malloc\n");
        rv = 1;
        goto cleanup;
    }
    
    sg_array = (struct ibv_sge*)
                        malloc(conn->device.rcqe*sizeof(struct ibv_sge));
    if (!sg_array) {
        error("malloc\n");
        rv = 1;
        goto cleanup;
    }
    
    for (i = 0; i < conn->device.rcqe; i++) {
        memset(&sg_array[i], 0, sizeof(struct ibv_sge));
        sg_array[i].addr   = (uint64_t)(conn->recv_mem[i].buf);
        sg_array[i].length = conn->recv_mem[i].len;
        sg_array[i].lkey   = conn->recv_mem[i].mr->lkey;
        
        memset(&wr_array[i], 0, sizeof(struct ibv_recv_wr));
        wr_array[i].wr_id   = i;
        wr_array[i].sg_list = &sg_array[i];
        wr_array[i].num_sge = 1;
        wr_array[i].next    = (i == conn->device.rcqe-1) ? NULL : 
                            &wr_array[i+1];
    }
    
    rv = ibv_post_recv(conn->qp, wr_array, &bad_wr);
    if (rv) {
        VERB_ERR("ibv_post_recv", rv);
        goto cleanup;
    }
    
    rv = 0;
cleanup:
    if (wr_array) {
        free(wr_array);
    }
    if (sg_array) {
        free(sg_array);
    }
    return rv;
}

static int
post_one_receive(conn_t *conn, int idx)
{
    int rv;
    struct ibv_recv_wr *bad_wr = NULL;
    struct ibv_recv_wr wr;
    struct ibv_sge sg;
    
    memset(&sg, 0, sizeof(struct ibv_sge));
    sg.addr   = (uint64_t)conn->recv_mem[idx].buf;
    sg.length = conn->recv_mem[idx].len;
    sg.lkey   = conn->recv_mem[idx].mr->lkey;
        
    memset(&wr, 0, sizeof(struct ibv_recv_wr));
    wr.wr_id   = idx;
    wr.sg_list = &sg;
    wr.num_sge = 1;
    
    rv = ibv_post_recv(conn->qp, &wr, &bad_wr);
    if (rv) {
        VERB_ERR("ibv_post_recv", rv);
        return 1;
    }
    return 0;
}

static void
disconnect(struct rdma_cm_id *id)
{    
    if (!id) return;
    if (id->channel) {
        //info("   # initiate disconnect ID=%p\n", id);
        if (id->verbs) {
            rdma_disconnect(id);
        }
        conn_t *conn = id->context;
        if (conn) {
            conn->init_disconnect = 1;
        }
    }
    else {
        if (id->context) {
            destroy_connection(id->context);
        }
        else {
            rdma_destroy_id(id);
        }
    }
}

//#define CONN_DEBUG
static void 
destroy_connection(conn_t *conn)
{
    send_buf_t *sb;
    if (!conn) return;

#ifdef CONN_DEBUG
    info_wtime("Destroy_connection\n");
#endif    
    
#ifdef CONN_DEBUG
    info("   destroying QP...");
#endif        
    destroy_qp(conn);
#ifdef CONN_DEBUG
    info("done\n");
#endif   

#ifdef CONN_DEBUG
    info("   dereg memory...");
#endif        
    deregister_memory(conn);
#ifdef CONN_DEBUG
    info("done\n");
#endif   

    /* Free list with send buffers */
#ifdef CONN_DEBUG
    info("   free send buffers...");
#endif        
    while (NULL != (sb = conn->conn_ctx.send_buf)) {
        conn->conn_ctx.send_buf = sb->next;
        sb->sh_buf->shared_count--;
        if (0 == sb->sh_buf->shared_count) { 
            free(sb->sh_buf); 
        }
        free(sb);
    }
#ifdef CONN_DEBUG
    info("done\n");
#endif   

#ifdef CONN_DEBUG
    info("   destroy CQs...");
#endif        
    if (conn->device.scq == conn->device.rcq) {
        if (NULL != conn->device.scq) {
            ibv_destroy_cq(conn->device.scq);
        }
    }
    else {
        if (NULL != conn->device.scq) {
            ibv_destroy_cq(conn->device.scq);
        }
        if (NULL != conn->device.rcq) {
            ibv_destroy_cq(conn->device.rcq);
        }
    }
#ifdef CONN_DEBUG
    info("done\n");
#endif

#ifdef CONN_DEBUG
    info("   dealloc PD...");
#endif        
    if (NULL != conn->device.pd) {
        ibv_dealloc_pd(conn->device.pd);
    }
#ifdef CONN_DEBUG
    info("done\n");
#endif

    if (conn->id) { 
#ifdef CONN_DEBUG
    info("   destroy ID %p...", conn->id);
#endif        
        rdma_destroy_id(conn->id);
#ifdef CONN_DEBUG
    info("done\n");
#endif
    }
    else {
        if (NULL != conn->device.context) {
            ibv_close_device(conn->device.context);
        }
    }
    free(conn);
}

static void 
destroy_qp(conn_t *conn)
{
    int rv;
    struct ibv_qp_attr attr;
    struct ibv_wc wc;

    if (!conn) return;
    if (!conn->qp) return;
    do {
        /* Move QP into the ERR state to cancel all outstanding work requests */
        memset(&attr, 0, sizeof(attr));
        attr.qp_state = IBV_QPS_ERR;
        rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_STATE);
        if (rv) {
            VERB_ERR("ibv_modify_qp", rv);
            break;
        }
        if (conn->device.scq) {
            while (ibv_poll_cq(conn->device.scq, 1, &wc) > 0);
        }
        if (conn->device.rcq) {
            while (ibv_poll_cq(conn->device.rcq, 1, &wc) > 0);
        }
        memset(&attr, 0, sizeof(attr));
        attr.qp_state = IBV_QPS_RESET;
        rv = ibv_modify_qp(conn->qp, &attr, IBV_QP_STATE);
        if (rv) {
            VERB_ERR("ibv_modify_qp", rv);
            break;
        }
    } while (0);

no_outstanding_wr:
    ibv_destroy_qp(conn->qp);
    conn->qp = NULL;
}

/**
 * Handle the completion status of a WC 
 */
static int
handle_work_completion(conn_t *conn, struct ibv_wc *wc)
{
    int rc;
    uint64_t wr_id = wc->wr_id;

    /* Verify completion status */
    switch(wc->status) {
        case IBV_WC_SUCCESS:
            /* IBV_WC_SUCCESS: Operation completed successfully */
            return WC_SUCCESS;
        case IBV_WC_LOC_LEN_ERR:    //  Local Length Error
        case IBV_WC_LOC_QP_OP_ERR:  //  Local QP Operation Error
        case IBV_WC_LOC_EEC_OP_ERR: //  Local EE Context Operation Error
        case IBV_WC_LOC_PROT_ERR:   //  Local Protection Error   
        case IBV_WC_MW_BIND_ERR:    //  Memory Window Binding Error
        case IBV_WC_LOC_ACCESS_ERR: //  Local Access Error
        case IBV_WC_REM_ACCESS_ERR: //  Remote Access Error
        case IBV_WC_RNR_RETRY_EXC_ERR:  // RNR Retry Counter Exceeded
        case IBV_WC_LOC_RDD_VIOL_ERR:   // Local RDD Violation Error
        case IBV_WC_REM_INV_RD_REQ_ERR: // Remote Invalid RD Request
        case IBV_WC_REM_ABORT_ERR:  // Remote Aborted Error
        case IBV_WC_INV_EECN_ERR:   // Invalid EE Context Number
        case IBV_WC_INV_EEC_STATE_ERR:  // Invalid EE Context State Error
            /* Nothing to do with the failure of the remote side; 
               most likely a software bug */
            error("software bug: status %s (%d)\n",
                        ibv_wc_status_str(wc->status), wc->status);
            return WC_SOFTWARE_BUG;
        case IBV_WC_BAD_RESP_ERR:
            /* Bad Response Error - an unexpected transport layer 
            opcode was returned by the responder. */
        case IBV_WC_REM_INV_REQ_ERR:
            /* Remote Invalid Request Error: The responder detected an 
            invalid message on the channel. Possible causes include the 
            operation is not supported by this receive queue, insufficient 
            buffering to receive a new RDMA or Atomic Operation request, 
            or the length specified in an RDMA request is greater than 
            2^{31} bytes. Relevant for RC QPs. */
        case IBV_WC_FATAL_ERR:
            /* Fatal Error - WTF */
        case IBV_WC_RESP_TIMEOUT_ERR:
            /* Response Timeout Error */
        case IBV_WC_GENERAL_ERR:
            /* General Error: other error which isn’t one of the above errors. */
        case IBV_WC_REM_OP_ERR:
            /* Remote Operation Error: the operation could not be 
            completed successfully by the responder. Possible causes 
            include a responder QP related error that prevented the 
            responder from completing the request or a malformed WQE on 
            the Receive Queue. Relevant for RC QPs. */
            error("error: status %s (%d)\n",
                        ibv_wc_status_str(wc->status), wc->status);
            return WC_ERROR;
        case IBV_WC_WR_FLUSH_ERR:
            /* Work Request Flushed Error: A Work Request was in 
            process or outstanding when the QP transitioned into the 
            Error State. */
        case IBV_WC_RETRY_EXC_ERR:
            /* Transport Retry Counter Exceeded: The local transport 
            timeout retry counter was exceeded while trying to send this 
            message. This means that the remote side didn’t send any Ack 
            or Nack. If this happens when sending the first message, 
            usually this mean that the connection attributes are wrong or 
            the remote side isn’t in a state that it can respond to messages. 
            If this happens after sending the first message, usually it 
            means that the remote QP isn’t available anymore. */
            /* REMOTE SIDE IS DOWN */
            info("[FAILURE]\n");
            return WC_FAILURE;
    }

    return rc; 
}

/** 
 * source: OpenMPI source
   Horrible.  :-( Per the thread starting here:
   http://lists.openfabrics.org/pipermail/general/2008-June/051822.html,
   we can't rely on the value reported by the device to determine the
   maximum max_inline_data value.  So we have to search by looping
   over max_inline_data values and trying to make dummy QPs.  Yuck! 
 */
static int 
find_max_inline(struct ibv_context *context, 
                struct ibv_pd *pd,
                uint32_t *max_inline_arg)
{
    int rc;
    struct ibv_qp *qp = NULL;
    struct ibv_cq *cq = NULL;
    struct ibv_qp_init_attr init_attr;
    uint32_t max_inline_data;
    
    *max_inline_arg = 0;

    /* Make a dummy CQ */
    cq = ibv_create_cq(context, 1, NULL, NULL, 0);
    if (NULL == cq) {
        return 1;
    }
    
    /* Setup the QP attributes */
    memset(&init_attr, 0, sizeof(init_attr));
    init_attr.qp_type = IBV_QPT_RC;
    init_attr.send_cq = cq;
    init_attr.recv_cq = cq;
    init_attr.srq = 0;
    init_attr.cap.max_send_sge = 1;
    init_attr.cap.max_recv_sge = 1;
    init_attr.cap.max_recv_wr = 1;
    
    /* Loop over max_inline_data values; just check powers of 2 --
       that's good enough */
    init_attr.cap.max_inline_data = max_inline_data = 1 << 20;
    rc = 1;
    while (max_inline_data > 0) {
        qp = ibv_create_qp(pd, &init_attr);
        if (NULL != qp) {
            *max_inline_arg = max_inline_data;
            ibv_destroy_qp(qp);
            rc = 0;
            break;
        }
        max_inline_data >>= 1;
        init_attr.cap.max_inline_data = max_inline_data;
    }
    
    /* Destroy the temp CQ */
    if (NULL != cq) {
        ibv_destroy_cq(cq);
    }

    return rc;
}

#endif
