/**                                                                                                      
 * AllConcur
 * 
 * Network module -- TCP
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <netinet/tcp.h>
#include <sys/ioctl.h>

#include <debug.h>
#include <ac_timer.h>
#include <ac_net.h>
#include <ac_tcp.h>

/* ================================================================== */
/* Type definitions */
#if 1

struct conn_t {
    conn_ctx_t      conn_ctx;
    int sfd;
    int bytes_on_socket;
    uint32_t        rbuf_len;
    void            *recv_buf;
};
typedef struct conn_t conn_t;

struct channel_t {
    ev_io io;
    int fd;
    conn_data_t *cd;
};
typedef struct channel_t channel_t;

struct w_connect_t {
    ev_io io;
    uint32_t next_idx;
};
typedef struct w_connect_t w_connect_t;

struct ud_ep_t {
    struct sockaddr_storage addr;
    socklen_t addr_len;
};
typedef struct ud_ep_t ud_ep_t;

#define DEFAULT_BUF_SIZE 512

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

/* Synchronous operations */
static int 
ac_tcp_connect(ep_t* ep);
static int 
ac_tcp_send(void *conn_id, void *buf_idx, uint32_t len);
static int
ac_tcp_recv(void *conn_id, void *recv_buf, uint32_t len);
static void 
ac_tcp_disconnect(void *conn_id);

/* Asynchronous operations */
static void* 
ac_tcp_ilisten(conn_data_t *cd);
static int 
ac_tcp_iconnect(ep_t* ep, void *channel);
static int 
ac_tcp_isend(ep_t *ep, shared_buf_t *sh_buf);
static int 
ac_tcp_done_sending(ep_t *ep);
static int 
ac_tcp_ongoing_bytes(ep_t *ep);
static void
ac_tcp_destroy_ch(void *ch);

/* Unreliable datagrams */
static int
ac_tcp_ud_setup(ud_t* ud);
static int 
ac_tcp_sendto(ud_t* ud, void *endpoint, void *buf, uint32_t buf_len);
static int 
ac_tcp_cmp_ud_eps(void *left, void *right);
static int 
ac_tcp_cp_ud_ep(void **dest, void *src);
static char*
ac_tcp_ud_ep_to_str(char *str, uint32_t len, void *endpoint);
static void
ac_tcp_print_ud_ep(void *endpoint);

/* Callbacks */
static void 
accept_cb(EV_P_ struct ev_io *w, int revents);
static void
connect_cb(EV_P_ struct ev_io *w, int revents);
static void 
send_recv_cb(EV_P_ struct ev_io *w, int revents);
static void 
on_sending_data(EV_P_ struct ev_io *w);
static void 
on_receiving_data(EV_P_ struct ev_io *w);
static void 
read_ud_cb(EV_P_ struct ev_io *w, int revents);

/* Others */
static void 
set_buffer_len(conn_t *conn, conn_data_t *cd);
static int
register_memory(conn_t *conn);
static void 
deregister_memory(conn_t *conn);
static int
manage_connection(conn_t *conn);
static void
disconnect(conn_t *conn);

#endif

/* ================================================================== */
/* Global variables */
#if 1

/* module registration data structure (TCP) */
ac_net_module_t ac_tcp_mod = {
    .name            = "TCP",
    .desc            = "Mode tcp uses TCP for data transmission.",
    .bytes_to_send   = 0,
    .ev_loop         = NULL,
    .terminate       = NULL,
    .get_sbuf        = NULL,
    .get_sbuf_len    = NULL,
    .connect         = ac_tcp_connect,
    .send            = ac_tcp_send,
    .receive         = ac_tcp_recv,
    .disconnect      = ac_tcp_disconnect,
    .ilisten         = ac_tcp_ilisten,
    .iconnect        = ac_tcp_iconnect,
    .poll_ch         = NULL,
    .poll_recv       = NULL,
    .isend           = ac_tcp_isend,
    .poll_send       = NULL,
    .done_sending    = ac_tcp_done_sending,
    .ongoing_bytes   = ac_tcp_ongoing_bytes,
    .on_send_completed = NULL,
    .create_ch       = NULL,
    .destroy_ch      = ac_tcp_destroy_ch,
    .wait_for_disconnects = NULL,
    .ud_setup        = ac_tcp_ud_setup,
    .sendto          = ac_tcp_sendto,
    .poll_sendto     = NULL,
    .ud_poll_recv    = NULL,
    .cmp_ud_eps      = ac_tcp_cmp_ud_eps,
    .cp_ud_ep        = ac_tcp_cp_ud_ep,
    .ud_ep_to_str    = ac_tcp_ud_ep_to_str,
    .print_ud_ep     = ac_tcp_print_ud_ep,
};

#endif

/* ================================================================== */
/* Global functions */
#if 1

void ac_tcp_reg_module(struct ev_loop *loop, 
                       void (*terminate)(int), 
                       int timer, 
                       void (*on_send_completed)())
{
    ac_net_mod = &ac_tcp_mod;
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
/* Synchronous operations */
/**
 * Connect to a remote host (synchronous)
 */
static int 
ac_tcp_connect(ep_t* ep)
{ 
    struct addrinfo hints, *servinfo, *p;
    int rv, yes, sfd;
    conn_t *conn = NULL;
    
    if (!ep) {
        error("ep is NULL\n");
        return 1;
    }
    
    if (!ep->conn) {
        ep->conn = conn = (conn_t*)malloc(sizeof(conn_t));
        if (!conn) {
            error("malloc\n");
            return 1;
        }
        memset(conn, 0, sizeof(conn_t));
        conn->sfd = -1;
        ep->cd.rcount = 0;
        set_buffer_len(conn, &ep->cd);
        /* Active side */
        conn->conn_ctx.active = 1;
        conn->conn_ctx.ep = ep;
    }
    else {
        conn = (conn_t*)ep->conn;
        if (-1 != conn->sfd) {
            close(conn->sfd);
            conn->sfd = -1;
        }
    }
    
    /* Obtain address(es) matching host/port */
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;                /* Allow IPv4 or IPv6 */
    hints.ai_socktype = SOCK_STREAM;             /* Stream socket */
    rv = getaddrinfo(ep->cd.ei.host, ep->cd.ei.port, &hints, &servinfo);
    if (rv) {
        error("getaddrinfo: %s\n", gai_strerror(rv));
        return 1;
    }
    /* Loop until you connect */
    while (1) {
        /* getaddrinfo() returns a list of address structures.
           Try each address until we successfully connect(2).
           If socket(2) (or connect(2)) fails, we (close the socket
           and) try the next address. */
        for(p = servinfo; p != NULL; p = p->ai_next) {
            conn->sfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
            if (-1 == conn->sfd)
                continue;
            
            rv = connect(conn->sfd, p->ai_addr, p->ai_addrlen);
            if (-1 == rv) {
                close(conn->sfd);
                conn->sfd = -1;
                continue;
            }
            break;
        }
        if (p != NULL) {
            break;
        }
    }

    /* Disable Nagle's algorithm -- send ASAP */
    yes = 1;
    if (setsockopt(conn->sfd, 
                IPPROTO_TCP, TCP_NODELAY, &yes, sizeof(int)) == -1) 
    {
        error("[%d] setsockopt() (%s)\n", errno, strerror(errno));
        rv = 0;
        goto cleanup;
    }
    
    rv = register_memory(conn);
    if (rv) {
        error("register_memory\n");
        goto cleanup;
    }
    rv = 0;
    goto cleanup;
    
cleanup:    
    if (servinfo) {
        freeaddrinfo(servinfo);
    }
    return rv;
}

static int 
ac_tcp_send(void *conn_id, void *buf_idx, uint32_t len)
{
    int numbytes; 
    
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return 1;
    }
    if (!buf_idx) {
        error("no buffer\n");
        return 1;
    }
    
    numbytes = send(conn->sfd, buf_idx, len, 0);
    if (-1 == numbytes) {
        error("[%d] send (%s)\n", errno, strerror(errno));
        return 1;
    }
    return 0;
}

static int
ac_tcp_recv(void *conn_id, void *recv_buf, uint32_t len)
{
    int numbytes; 
    
    conn_t *conn = (conn_t*)conn_id;
    if (!conn) {
        error("conn_id is NULL\n");
        return 1;
    }
    if (!recv_buf) {
        error("no buffer\n");
        return 1;
    }
    
    numbytes = recv(conn->sfd, recv_buf, len, MSG_WAITALL);
    if (numbytes < 0) {
        error("recv (%s)\n", strerror(errno));
        return 1;
    }
    else if (numbytes == 0) {
        info("server disconnect\n");
        return 1;
    }
    
    return 0;
}

static void 
ac_tcp_disconnect(void *conn_id)
{
    disconnect((conn_t*)conn_id);
    free(conn_id);
}

/* ================================================================== */
/* Asynchronous operations */

/**
 * Listen for TCP connections
 */
static void* 
ac_tcp_ilisten(conn_data_t *cd)
{
    struct addrinfo hints, *servinfo, *p = NULL;
    ep_id_t ei;
    int yes, rv, port_num;
    channel_t *channel = NULL;
    
    channel = (channel_t*)malloc(sizeof(channel_t));
    if (!channel) {
        error("malloc\n");
        return NULL;
    }
    memset(channel, 0, sizeof(channel_t));

    
    channel->cd = malloc(sizeof(conn_data_t));
    if (!channel->cd) {
        error("malloc\n");
        goto exit_with_error;
    }
    memcpy(channel->cd, cd, sizeof(conn_data_t));
    
    while (!p) {
        memset(&hints, 0, sizeof(hints));
        hints.ai_family = AF_UNSPEC;                /* Allow IPv4 or IPv6 */
        hints.ai_socktype = SOCK_STREAM;
        hints.ai_flags = AI_PASSIVE;           /* For wildcard IP address */
    
        if ((rv = getaddrinfo(NULL, cd->ei.port, &hints, &servinfo)) != 0) {
            error("getaddrinfo: %s\n", gai_strerror(rv));
            goto exit_with_error;
        }
        /* getaddrinfo() returns a list of address structures.
           Try each address until we successfully bind(2).
           If socket(2) (or bind(2)) fails, we (close the socket
           and) try the next address. */
        for(p = servinfo; p != NULL; p = p->ai_next) {
            channel->fd = socket(p->ai_family, p->ai_socktype | SOCK_NONBLOCK,
                            p->ai_protocol);
            if (-1 == channel->fd)
                continue;
     
            /* setsockopt: 
               Eliminates some "ERROR on binding: Address already in use" 
               errors. */
            yes=1;
            if (setsockopt(channel->fd, SOL_SOCKET, SO_REUSEADDR, &yes, 
                            sizeof(int)) == -1) 
            {
                error("[%d] setsockopt() (%s)\n", errno, strerror(errno));
                goto exit_with_error;
            }
     
            if (bind(channel->fd, p->ai_addr, p->ai_addrlen) == 0) {
                break;                                         /* Success */
            }
            rv = getnameinfo(p->ai_addr, p->ai_addrlen, ei.host, NI_MAXHOST,
                            ei.port, NI_MAXSERV, NI_NUMERICSERV);
            info("Warning: bind to %s:%s (%s)\n", ei.host, ei.port, strerror(errno));
            close(channel->fd); 
            channel->fd = -1;
            continue;
        }
        if (!p) {
            port_num = atoi(cd->ei.port);
            memset(cd->ei.port, 0, sizeof cd->ei.port);
            sprintf(cd->ei.port, "%d", (port_num+1));
            info("Could not bind to port %d; try port %s\n", port_num, cd->ei.port);
        }
    }  
        
    /* TCP -- wait for incoming connections */
    if (listen(channel->fd, MAX_CONNECTIONS) == -1) {
        error("[%d] listen (%s)\n", errno, strerror(errno));
        goto exit_with_error;
    }
    
    rv = getnameinfo(p->ai_addr, p->ai_addrlen, ei.host, NI_MAXHOST,
                        ei.port, NI_MAXSERV, NI_NUMERICSERV);
    info_wtime("Listening on %s:%s\n", ei.host, ei.port);
        
    /* Initialize and start a watcher to accept predecessors requests */
    ev_io_init(&channel->io, accept_cb, channel->fd, EV_READ);
    ev_set_priority(&channel->io, EV_MAXPRI-1);
    ev_io_start(ac_tcp_mod.ev_loop, &channel->io);
    goto cleanup;
    
exit_with_error:
    ac_tcp_destroy_ch(channel);
    channel = NULL;
cleanup:
    if (servinfo) {
        freeaddrinfo(servinfo);
    }
    return channel;
}

static int 
ac_tcp_iconnect(ep_t* ep, void *channel)
{
    struct addrinfo hints, *servinfo, *p;
    int rv, yes, sfd;
    conn_t *conn = NULL;
    
    if (!ep) {
        error("ep is NULL\n");
        return 1;
    }
    
    if (NULL == ep->conn) {
        ep->conn = conn = (conn_t*)malloc(sizeof(conn_t));
        if (!conn) {
            error("malloc\n");
            return 1;
        }
        memset(conn, 0, sizeof(conn_t));
        conn->sfd = -1;
        set_buffer_len(conn, &ep->cd);
        /* Active side */
        conn->conn_ctx.active = 1;
        conn->conn_ctx.ep = ep;
    }
    else {
        conn = (conn_t*)ep->conn;
        if (-1 != conn->sfd) {
            close(conn->sfd);
            conn->sfd = -1;
        }
    }
       
    /* Obtain address(es) matching host/port */
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;                /* Allow IPv4 or IPv6 */
    hints.ai_socktype = SOCK_STREAM;             /* Stream socket */
    rv = getaddrinfo(ep->cd.ei.host, ep->cd.ei.port, &hints, &servinfo);
    if (rv) {
        error("getaddrinfo: %s\n", gai_strerror(rv));
        return 1;
    }
    /* getaddrinfo() returns a list of address structures.
       Try each address until we successfully connect(2).
       If socket(2) (or connect(2)) fails, we (close the socket
       and) try the next address. */
    for(p = servinfo; p != NULL; p = p->ai_next) {
        conn->sfd = socket(p->ai_family, p->ai_socktype | SOCK_NONBLOCK,
                            p->ai_protocol);
        if (-1 == conn->sfd) continue;

        rv = connect(conn->sfd, p->ai_addr, p->ai_addrlen);
        if (-1 == rv) {
            if ((errno == EINPROGRESS) || (errno == EALREADY)) {
                /* Connection in progress */
                ev_io_init(&conn->conn_ctx.proto.tcp.io, 
                            connect_cb, conn->sfd, EV_WRITE);
                ev_set_priority(&conn->conn_ctx.proto.tcp.io, EV_MAXPRI-1);
                ev_io_start(ac_tcp_mod.ev_loop, &conn->conn_ctx.proto.tcp.io);
                rv = 0;
                goto cleanup;
            }
            close(conn->sfd);
            conn->sfd = -1;
            continue;
        }
        break;
    }
    if (p == NULL) {
        info("client: Could not connect\n");
        rv = 1;
        goto cleanup;
    }
    /* Manage connection */
    rv = manage_connection(conn);
    if (rv) {
        error("manage_connection");
        goto cleanup;
    }
    rv = 0;

cleanup:    
    if (servinfo) {
        freeaddrinfo(servinfo);
    }
    return rv;   
}

static int 
ac_tcp_isend(ep_t *ep, shared_buf_t *sh_buf) 
{
    int rv, numbytes = -1;
    uint32_t len = 0;
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
        if (send_ctx->outstanding_sends) {
            /* Cannot send message asynchronously -- drop it */
            info("Warning: Cannot send message asynchronously\n");
            return 0;
        }
    }

    if (send_ctx->outstanding_sends) {
        goto postpone_send;
    }
    
#ifdef STATS    
    HRT_TIMESTAMP_T t1, t2;
    uint64_t ticks;
    if (ac_net_mod->timer) {    
        HRT_GET_TIMESTAMP(t1);
    }
#endif
    numbytes = send(conn->sfd, sh_buf->buf, sh_buf->len, 0);
    if (-1 == numbytes) { 
        if (errno == ECONNRESET) {
            ac_ep_destroy(ep);
            return 0;
        }
        if ((errno != EAGAIN) && (errno != EWOULDBLOCK)) {
            error("[%d] send (%s)\n", errno, strerror(errno));
            ac_net_mod->terminate(1);
        }
        numbytes = 0;
    }
    else if (numbytes == sh_buf->len) {
//dump_bytes(sh_buf->buf, numbytes, "SENT_DATA");
#ifdef STATS    
        ac_tcp_mod.total_sent_bytes += numbytes;
        if (ac_net_mod->timer) {
            HRT_GET_TIMESTAMP(t2);
            HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
            ac_tcp_mod.sending_time += HRT_GET_USEC(ticks);
        }
       
#endif
        conn->bytes_on_socket += numbytes;
//info_wtime("[fd=%d] adding to send buffer: %d bytes\n", conn->sfd, numbytes);
        send_ctx->outstanding_sends=0;
        return 0;
    }
    else {
        conn->bytes_on_socket += numbytes;
    }
#ifdef STATS    
    ac_tcp_mod.total_sent_bytes += numbytes;  
    if (ac_net_mod->timer) {
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        ac_tcp_mod.sending_time += HRT_GET_USEC(ticks);
    }
#endif
    if (!send_ctx->buffering) {
        send_ctx->outstanding_sends=1;
        return 0;
    }
    
postpone_send:    
    /* Create a new send buffer for this shared buffer */
    sb = (send_buf_t*)malloc(sizeof(send_buf_t));
    if (NULL == sb) {
        error("malloc (%s)\n", strerror(errno));
        return 1;
    }
    sb->sh_buf = sh_buf;
    sh_buf->shared_count++;
    
    /* Set amount of already sent bytes */
    if (numbytes > 0) {
        sb->bytes_sent = (uint32_t)numbytes;
#ifdef MSG_FLOW
info("   sent partial data (%"PRIu32" bytes)\n", sb->bytes_sent);
#endif
//info_wtime("[fd=%d] adding to send buffer: %d bytes\n", conn->sfd, numbytes);
//info("[%p] -> ", conn); dump_bytes(sb->sh_buf->buf, numbytes, "SENT_DATA");
    }
    else {
        sb->bytes_sent = 0;
#ifdef MSG_FLOW
info("   queing\n");
#endif
    }
    ac_tcp_mod.bytes_to_send += sh_buf->len - sb->bytes_sent;
//info("[fd=%d] bytes_to_send=%d\n", conn->sfd, ac_tcp_mod.bytes_to_send);

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
    if (0 == send_ctx->outstanding_sends) {
        send_ctx->outstanding_sends = 1;
    }
    return 0;
}

static int 
ac_tcp_done_sending(ep_t *ep)
{
    if (!ep) {
        return 1;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        return 1;
    }
    ioctl(conn->sfd, TIOCOUTQ, &conn->bytes_on_socket);
    //info("[fd=%d] Bytes in send buffer: %d\n", conn->sfd, conn->bytes_on_socket);
    return (conn->bytes_on_socket == 0);
}

static int 
ac_tcp_ongoing_bytes(ep_t *ep)
{
    if (!ep) {
        return 1;
    }
    conn_t *conn = (conn_t*)ep->conn;
    if (!conn) {
        return 1;
    }
    ioctl(conn->sfd, TIOCOUTQ, &conn->bytes_on_socket);
    return conn->bytes_on_socket;
}

static void
ac_tcp_destroy_ch(void *ch)
{
    channel_t *channel = (channel_t*)ch;
    if (!channel) return;
    if (channel->fd != -1) {
        close(channel->fd);
    }
    ev_io_stop(ac_tcp_mod.ev_loop, &channel->io);
    if (channel->cd) {
        free(channel->cd);
        channel->cd = NULL;
    }
    free(channel);
}

/* ================================================================== */
/* Unreliable datagrams */
static int
ac_tcp_ud_setup(ud_t* ud)
{
    conn_t *conn = NULL;
    struct addrinfo hints, *servinfo, *p = NULL;
    ep_id_t ei;
    int yes, rv, port_num;
    
    if (!ud) {
        error("ud is NULL\n");
        return 1;
    }
    
    if (ud->conn) {
        disconnect(ud->conn);
    }
    ud->conn = conn = (conn_t*)malloc(sizeof(conn_t));
    if (!conn) {
        error("malloc\n");
        goto exit_with_error;
    }
    memset(conn, 0, sizeof(conn_t));
    conn->sfd = -1;
    set_buffer_len(conn, &ud->cd);
    /* Passive side */
    conn->conn_ctx.active = 0;
    conn->conn_ctx.ud = ud;
           
    while (!p) {
        memset(&hints, 0, sizeof(hints));
        hints.ai_family = AF_UNSPEC;                /* Allow IPv4 or IPv6 */
        hints.ai_socktype = SOCK_DGRAM;
        hints.ai_flags = AI_PASSIVE;           /* For wildcard IP address */
        rv = getaddrinfo(ud->cd.ei.host, ud->cd.ei.port, &hints, &servinfo);
        if (0 != rv) {
            error("getaddrinfo: %s\n", gai_strerror(rv));
            goto exit_with_error;
        }
        /* getaddrinfo() returns a list of address structures.
           Try each address until we successfully bind(2).
           If socket(2) (or bind(2)) fails, we (close the socket
           and) try the next address. */
        for(p = servinfo; p != NULL; p = p->ai_next) {
            conn->sfd = socket(p->ai_family, p->ai_socktype | SOCK_NONBLOCK,
                            p->ai_protocol);
            if (-1 == conn->sfd)
                continue;
     
            /* setsockopt: 
               Eliminates some "ERROR on binding: Address already in use" 
               errors. */
            yes=1;
            if (setsockopt(conn->sfd, SOL_SOCKET, SO_REUSEADDR, &yes, 
                            sizeof(int)) == -1) 
            {
                error("[%d] setsockopt() (%s)\n", errno, strerror(errno));
                goto exit_with_error;
            }
     
            if (bind(conn->sfd, p->ai_addr, p->ai_addrlen) == 0) {
                break;                                         /* Success */
            }
            rv = getnameinfo(p->ai_addr, p->ai_addrlen, ei.host, NI_MAXHOST,
                            ei.port, NI_MAXSERV, NI_NUMERICSERV);
            info("Warning: bind to %s:%s (%s)\n", ei.host, ei.port, strerror(errno));
            close(conn->sfd); 
            conn->sfd = -1;
            continue;
        }
        if (!p) {
            port_num = atoi(ud->cd.ei.port);
            memset(ud->cd.ei.port, 0, sizeof ud->cd.ei.port);
            sprintf(ud->cd.ei.port, "%d", (port_num+1));
            info("Could not bind to port %d; try port %s\n", port_num, ud->cd.ei.port);
        }
    }
    
    rv = getnameinfo(p->ai_addr, p->ai_addrlen, ei.host, NI_MAXHOST,
                        ei.port, NI_MAXSERV, NI_NUMERICSERV);
    info_wtime("Listening for datagrams on %s:%s\n", ei.host, ei.port);
    
    ud->ud_info.len = sizeof(ud_ep_t);
    ud->ud_info.endpoint = malloc(ud->ud_info.len);
    if (!ud->ud_info.endpoint) {
        error("malloc\n");
        goto exit_with_error;
    }
    memset(ud->ud_info.endpoint, 0, ud->ud_info.len);
    ud_ep_t *ud_ep = ud->ud_info.endpoint;
    ud_ep->addr_len = p->ai_addrlen;
    memcpy(&ud_ep->addr, p->ai_addr, p->ai_addrlen);
               
    rv = register_memory(conn);
    if (rv) {
        error("register_memory\n");
        disconnect(conn);
        goto exit_with_error;
    }
        
    /* Initialize and start a watcher to read incoming data */
    ev_io *io = &conn->conn_ctx.proto.tcp.io;
    ev_io_init(io, read_ud_cb, conn->sfd, EV_READ);
    ev_set_priority(io, EV_MAXPRI-1);
    ev_io_start(ac_tcp_mod.ev_loop, io);
    rv = 0;
    goto cleanup;
    
exit_with_error:
    rv = 1;
cleanup:    
    if (servinfo) {
        freeaddrinfo(servinfo);
    }
    return rv; 
}

static int 
ac_tcp_sendto(ud_t* ud, void *endpoint, void *buf, uint32_t buf_len)
{
    int numbytes;
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
    
    numbytes = sendto(conn->sfd, buf, buf_len, 0, 
            (struct sockaddr *)&ud_ep->addr, ud_ep->addr_len);
    if (numbytes == buf_len) {
        return 0;
    }
    else if (-1 == numbytes) {
        if ((errno == EAGAIN) || (errno == EWOULDBLOCK)) {
            /* Cannot send -- just drop it */
            return 0;
        }
        error("[%d] send (%s)\n", errno, strerror(errno));
        return 1;
    }
}

static int 
ac_tcp_cmp_ud_eps(void *left, void *right)
{
    int rv;
    ud_ep_t *ud_ep_left = (ud_ep_t*)left;
    ud_ep_t *ud_ep_right = (ud_ep_t*)right;
    
    if (ud_ep_left->addr_len != ud_ep_right->addr_len) {
        return 1;
    }
    
    rv = memcmp(&ud_ep_left->addr, &ud_ep_right->addr, ud_ep_left->addr_len);
    if (rv) {
        return 1;
    }
    return 0;
}

static int 
ac_tcp_cp_ud_ep(void **dest, void *src)
{
    *dest = malloc(sizeof(ud_ep_t));
    if (!*dest) {
        error("malloc\n");
        return 1;
    }
    memcpy(*dest, src, sizeof(ud_ep_t));
    return 0;
}

static char*
ac_tcp_ud_ep_to_str(char *str, uint32_t len, void *endpoint)
{
    char ipstr[INET6_ADDRSTRLEN];
    void *addr;
    uint16_t port;
    ud_ep_t *ud_ep = (ud_ep_t*)endpoint;

    if (!endpoint) return "";
    if (len < INET6_ADDRSTRLEN + 8) return "";
    
    if (ud_ep->addr.ss_family == AF_INET) {
        struct sockaddr_in *ipv4 = (struct sockaddr_in*)&ud_ep->addr;
        addr = &(ipv4->sin_addr);
        port = ntohs(ipv4->sin_port);
    }
    else if (ud_ep->addr.ss_family == AF_INET6) {
        struct sockaddr_in6 *ipv6 = (struct sockaddr_in6*)&ud_ep->addr;
        addr = &(ipv6->sin6_addr);
        port = ntohs(ipv6->sin6_port);
    }
    inet_ntop(ud_ep->addr.ss_family, addr, ipstr, INET6_ADDRSTRLEN);
    
    sprintf(str, "%s:%"PRIu32, ipstr, port);

    return str;
}

static void
ac_tcp_print_ud_ep(void *endpoint)
{
    char ipstr[INET6_ADDRSTRLEN];
    void *addr;
    uint16_t port;
    ud_ep_t *ud_ep = (ud_ep_t*)endpoint;
    if (!endpoint) return;
    
    if (ud_ep->addr.ss_family == AF_INET) {
        struct sockaddr_in *ipv4 = (struct sockaddr_in*)&ud_ep->addr;
        addr = &(ipv4->sin_addr);
        port = ntohs(ipv4->sin_port);
    }
    else if (ud_ep->addr.ss_family == AF_INET6) {
        struct sockaddr_in6 *ipv6 = (struct sockaddr_in6*)&ud_ep->addr;
        addr = &(ipv6->sin6_addr);
        port = ntohs(ipv6->sin6_port);
    }
    inet_ntop(ud_ep->addr.ss_family, addr, ipstr, sizeof ipstr);
    
    info("%s:%"PRIu32, ipstr, port);
}

/* ================================================================== */
/* Callbacks */
/**
 * Accept connection from predecessors
 * Called when the file descriptor w->fd is readable
 */
static void 
accept_cb(EV_P_ struct ev_io *w, int revents)
{
    int sfd, rv, yes;
    struct sockaddr_storage their_addr;
    socklen_t sin_size;
    char host[NI_MAXHOST];
    char port[NI_MAXSERV];
    conn_t *conn = NULL;
    ep_t *ep = NULL;
    
    channel_t *channel = (channel_t*)w;
    
    if (EV_ERROR & revents) {
        error("[%d] got invalid event (%s)\n", errno, strerror(errno));
        return;
    }
    
    /* Accept predecessor (receiving side) */
    sin_size = sizeof(their_addr);
    sfd = accept(w->fd, (struct sockaddr *)&their_addr, &sin_size);
    if (sfd < 0) {
        if ((errno == EAGAIN) || (errno == EWOULDBLOCK)) {
            return;
        }
        error("[%d] accept (%s)\n", errno, strerror(errno));
        return;
    }
    rv = getnameinfo((struct sockaddr *)&their_addr,
                sin_size, host, NI_MAXHOST,
                port, NI_MAXSERV, NI_NUMERICSERV);
    info("Accepting connection from %s:%s\n", host, port);
   
    if (0 != set_blocking(sfd, 0)) {
        error("set_blocking\n");
        close(sfd);
        return;
    }

    /* Disable Nagle's algorithm -- send ASAP */
#if 1   
    yes = 1;
    if (setsockopt(sfd, 
                IPPROTO_TCP, TCP_NODELAY, &yes, sizeof(int)) == -1) 
    {
        error("[%d] setsockopt() (%s)\n", errno, strerror(errno));
        close(sfd);
        return;
    }
#endif
    
    /* New connection */
    conn = (conn_t*)malloc(sizeof(conn_t));
    if (!conn) {
        error("malloc\n");
        return;
    }
    memset(conn, 0, sizeof(conn_t));
    conn->sfd = sfd;
    conn->rbuf_len = channel->cd->rbuf_len;
    /* Passive side */
    conn->conn_ctx.active = 0;
    
    rv = register_memory(conn);
    if (rv) {
        error("register_memory\n");
        disconnect(conn);
        free(conn);
        conn = NULL;
        return;
    }
    
    /* Add connection to the list of servers */
    ep = (ep_t*)(channel->cd->on_connection(conn));
    if (NULL == ep) {
        error("on_connection");
        return;
    }
    ep->cd.handle_data = channel->cd->handle_data;
    ep->cd.destroy_ep_data = channel->cd->destroy_ep_data;
    conn->conn_ctx.ep = ep;

    /* Start IO watcher */
    ev_io_init(&conn->conn_ctx.proto.tcp.io, send_recv_cb, conn->sfd, EV_READ | EV_WRITE);
    ev_set_priority(&conn->conn_ctx.proto.tcp.io, EV_MAXPRI-1);
    ev_io_start(EV_A_ &conn->conn_ctx.proto.tcp.io);
}

/**
 * Handles connections to successors
 * Called when the file descriptor w->fd is writable
 */
static void
connect_cb(EV_P_ struct ev_io *w, int revents)
{
    int rv;
    socklen_t len;
    conn_t *conn = (conn_t*)w;
    ep_t *ep = conn->conn_ctx.ep;
    
    if (!ep) {
        error("ep is NULL\n");
        ac_net_mod->terminate(1);
    }
    
    /* Stop watcher (note: the socket is closed somewhere else) */
    ev_io_stop(EV_A_ w);

    /* Check error code of connect() */
    len = sizeof(errno);
    getsockopt(w->fd, SOL_SOCKET, SO_ERROR, &errno, &len);
    if (0 != errno) {
        if (ECONNREFUSED == errno) {
            /* No-one listening on the remote address -- the remote server 
               is either not yet listening or is failed; retry to connect */
            rv = ac_handle_ep_error(ep);
            if (rv) {
                error("ac_handle_ep_error\n");
                ac_net_mod->terminate(1);
            }
            return;
        }
        error("cannot connect to %s:%s (%s)\n", 
                    ep->cd.ei.host, ep->cd.ei.port, strerror(errno));
        ac_net_mod->terminate(1);
    }
    
    /* Manage connection */
    rv = manage_connection(conn);
    if (rv) {
        error("manage_connection");
        ac_net_mod->terminate(1);
    }
}

/**
 * Send/receive messages
 * Called when the file descriptor w->fd is writable/readable
 */
static void 
send_recv_cb(EV_P_ struct ev_io *w, int revents)
{
    if (EV_READ & revents) {
        /* incomming message */
        on_receiving_data(EV_A_ w);
    }
    else if (EV_WRITE & revents) {
        /* outgoing message */
        on_sending_data(EV_A_ w);
    }
    else if (EV_ERROR & revents) {
        error("[%d] got invalid event (%s)\n", errno, strerror(errno));
        return;
    }
}

/**
 * Send message callback
 * The send buffer is writable 
 */
static void 
on_sending_data(EV_P_ struct ev_io *w)
{
    conn_t *conn = (conn_t*)w;
    conn_ctx_t *send_ctx = &conn->conn_ctx;
    send_buf_t *sb, *next;
    uint64_t len;
    int numbytes, rv;

    /* I/O watchers check whether a file descriptor is readable or writable 
     * in each iteration of the event loop, or, more precisely, when reading 
     * would not block the process and writing would at least be able to write 
     * some data. 
     * -> need to avoid calling on_send_completed all the time */
    if (!send_ctx->send_buf &&      // no queued messages to send
       !conn->bytes_on_socket)      // no bytes in the socket buffer
    {
        return;
    }

#ifdef STATS    
    HRT_TIMESTAMP_T t1, t2;
    uint64_t ticks;
    if (ac_net_mod->timer) {    
        HRT_GET_TIMESTAMP(t1);
    }
#endif 
//info("[fd=%d] writable event\n", conn->sfd);   
    sb = send_ctx->send_buf;
    while (sb != NULL) {
        /* Send the buffer -- non-blocking */
        len = sb->sh_buf->len - sb->bytes_sent;
        numbytes = send(conn->sfd, sb->sh_buf->buf+sb->bytes_sent, len, 0);
        if (numbytes == len) {
#ifdef STATS    
            ac_tcp_mod.total_sent_bytes += numbytes;
#endif   
            conn->bytes_on_socket += numbytes;
//info("[%p] -> ", conn); dump_bytes(sb->sh_buf->buf+sb->bytes_sent, numbytes, "SENT_DATA");
            ac_tcp_mod.bytes_to_send -= numbytes;
//info_wtime("[fd=%d] adding to send buffer: %d bytes (%d remaining)\n", conn->sfd, numbytes, ac_tcp_mod.bytes_to_send);
            /* Remove myself from the shared pointer count */
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
        else if (-1 == numbytes) {
            if (errno == ECONNRESET) {
                ac_ep_destroy(send_ctx->ep);
                return;
            }
            if ((errno != EAGAIN) && (errno != EWOULDBLOCK)) {
                error("[%d] send (%s)\n", errno, strerror(errno));
                ac_net_mod->terminate(1);
            }
        }
        else if (numbytes < len) {
//info("[%p] -> ", conn); dump_bytes(sb->sh_buf->buf+sb->bytes_sent, numbytes, "SENT_DATA");
            conn->bytes_on_socket += numbytes;
            sb->bytes_sent += numbytes;
            ac_tcp_mod.bytes_to_send -= numbytes;
//info_wtime("[fd=%d] adding to send buffer: %d bytes (%d remaining)\n", conn->sfd, numbytes, ac_tcp_mod.bytes_to_send);
#ifdef STATS    
            ac_tcp_mod.total_sent_bytes += numbytes;
#endif            
            break;
        }
    }  

#ifdef STATS    
    if (ac_net_mod->timer) {
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        ac_tcp_mod.sending_time += HRT_GET_USEC(ticks);
    }
#endif
    if (!ac_tcp_mod.bytes_to_send) {
        /* No queued messages to send */
        send_ctx->outstanding_sends = 0;
        ioctl(conn->sfd, TIOCOUTQ, &conn->bytes_on_socket);
        if (conn->bytes_on_socket == 0 || 
                (send_ctx->ep->mtu_sent && conn->bytes_on_socket <= MTU_MSG_SIZE)) {
            /* No bytes in the socket's send buffer */
            if (ac_tcp_mod.on_send_completed) {
                /* Send completed */
                ac_tcp_mod.on_send_completed();   
            }
        }
    }
}

/**
 * Read data from server
 */
static void 
on_receiving_data(EV_P_ struct ev_io *w)
{
    ssize_t read;
    conn_t *conn = (conn_t*)w;
    ep_t *ep = conn->conn_ctx.ep;
    int yes, rv;

#ifdef STATS      
    HRT_TIMESTAMP_T t1, t2;
    uint64_t ticks;
    if (ac_net_mod->timer) {    
        HRT_GET_TIMESTAMP(t1);
    }
#endif 
    
    /* Set TCP_QUICKACK flag */
    yes = 1;
    setsockopt(w->fd, IPPROTO_TCP, TCP_QUICKACK, &yes, sizeof(yes));
    
    /* Read data */
    read = recv(w->fd, conn->recv_buf, conn->rbuf_len, 0);
    
    /* Set TCP_QUICKACK flag */
    yes = 1;
    setsockopt(w->fd, IPPROTO_TCP, TCP_QUICKACK, &yes, sizeof(yes));

    if (read < 0) {
        error("[%d] read (%s)\n", errno, strerror(errno));
        return;
    }
    else if (read == 0) {
        ac_ep_destroy(ep);
        return;
    }
#ifdef STATS        
    ac_tcp_mod.total_recv_bytes += read;
    if (ac_net_mod->timer) {
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        ac_tcp_mod.receiving_time += HRT_GET_USEC(ticks);
    }
#endif
//info_wtime("Received %zd bytes\n", read);  dump_bytes(conn->recv_buf, read, "RECV_DATA");
    
    /* Received data into buffer conn->recv_bufs[wc->wr_id] */
    ep->cd.handle_data(ep, conn->recv_buf, read);
}

static void 
read_ud_cb(EV_P_ struct ev_io *w, int revents)
{
    ssize_t read;    
    ud_ep_t ud_ep;
    conn_t *conn = (conn_t*)w;
    ud_t* ud = (ud_t*)conn->conn_ctx.ud;
    int rv;
    
    //channel->cd->handle_data;
    
    ud_ep.addr_len = sizeof(struct sockaddr_storage);
    read = recvfrom(w->fd, conn->recv_buf, conn->rbuf_len,
                    0, (struct sockaddr *) &ud_ep.addr, &ud_ep.addr_len);
    if (read < 0) {
        if ((errno == EAGAIN) || (errno == EWOULDBLOCK)) {
            return;
        }
        error("[%d] read (%s)\n", errno, strerror(errno));
        ac_net_mod->terminate(1);
    }
    
    ud->cd.handle_data(&ud_ep, conn->recv_buf, read);
}

/* ================================================================== */
/* Others */
static void 
set_buffer_len(conn_t *conn, conn_data_t *cd)
{    
    if (cd->rcount) {
        conn->rbuf_len = cd->rbuf_len * cd->rcount;
        if (conn->rbuf_len == 0) {
            conn->rbuf_len = DEFAULT_BUF_SIZE;
        }
    }
    else {
        conn->rbuf_len = 0;
    }
}

static int
register_memory(conn_t *conn)
{         
    /* Register memory for recv buffer */    
    if ((conn->rbuf_len) && (!conn->recv_buf)) {
        conn->recv_buf = (uint8_t*)malloc(conn->rbuf_len);
        if (!conn->recv_buf) {
            error("malloc\n");
            return 1;
        }
        memset(conn->recv_buf, 0, conn->rbuf_len);
    }
    
    return 0;
}

static void 
deregister_memory(conn_t *conn)
{   
    if (NULL != conn->recv_buf) {
        free(conn->recv_buf);
        conn->recv_buf = NULL;
    }
}

static int
manage_connection(conn_t *conn)
{
    int rv, yes;
    ep_t *ep = conn->conn_ctx.ep;
    
    /* Sending side */
    rv = register_memory(conn);
    if (rv) {
        error("register_memory\n");
        return 1;
    }
    
    /* Start IO watcher */
    ev_io_init(&conn->conn_ctx.proto.tcp.io, send_recv_cb, conn->sfd, EV_READ | EV_WRITE);
    ev_set_priority(&conn->conn_ctx.proto.tcp.io, EV_MAXPRI-1);
    ev_io_start(ac_tcp_mod.ev_loop, &conn->conn_ctx.proto.tcp.io);

    /* Disable Nagle's algorithm -- send ASAP */
    yes = 1;
    if (setsockopt(conn->sfd, 
                IPPROTO_TCP, TCP_NODELAY, &yes, sizeof(int)) == -1) 
    {
        error("[%d] setsockopt() (%s)\n", errno, strerror(errno));
        return 1;
    }
    
    if (NULL == ep->cd.on_connection(conn)) {
        error("on_connection\n");
        return 1;
    }
    
    return 0; 
}

static void
disconnect(conn_t *conn)
{
    send_buf_t *sb;
    
    if (NULL == conn) return;
    deregister_memory(conn);
    if (conn->sfd != -1) {
        close(conn->sfd);
        conn->sfd = -1;
    }
    /* Free list with send buffers */
    while (NULL != (sb = conn->conn_ctx.send_buf)) {
        conn->conn_ctx.send_buf = sb->next;
        sb->sh_buf->shared_count--;
        if (0 == sb->sh_buf->shared_count) { 
            free(sb->sh_buf); 
        }
        free(sb);
    }
    ev_io_stop(ac_tcp_mod.ev_loop, &conn->conn_ctx.proto.tcp.io);
}

#endif
