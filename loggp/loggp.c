/**                                                                                                      
 * AllConcur
 * 
 * LogGP parameter estimation
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <math.h>
#include <getopt.h>

#include <net/tcp/include/ac_tcp.h>
#include <net/ibv/include/ac_ibv.h>

#include <ac_net.h>
#include <ac_timer.h>
#include <debug.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define N 16
//#define N 5
#define MEASURE_COUNT 1000
//#define MEASURE_COUNT 5

#define PRTT_1_0_S 1
#define PRTT_N_D_S 2
#define PRTT_N_0_S 3

struct loggp_server_t {
    double *x;
    double *y;
    uint64_t ticks[MEASURE_COUNT];
    double prtt_1_0_s, prtt_n_d_s, prtt_n_0_s, L;
    uint32_t measure_count;
    HRT_TIMESTAMP_T t1, t2;
    uint32_t size;
    uint32_t n, i;
    double delay;
    uint32_t byte_count;
    char state;
};
typedef struct loggp_server_t loggp_server_t;

struct loggp_client_t {
    uint32_t measure_count;
    uint32_t size;
    uint32_t n;
    uint32_t byte_count;
    char state;
};
typedef struct loggp_client_t loggp_client_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

FILE *dbg_stream;
FILE *out_stream;
unsigned long long g_timerfreq;
int client;

int net_type;
struct ev_loop *loop; 
ev_idle w_poll;                       /* Idle watcher for polling */
ac_net_module_t *ac_net_mod;

void *channel;
ep_t *ep_list;
int recv_sigint;

const uint32_t min_size = 1;
//const uint32_t max_size = 1048576; // 128 KiB
const uint32_t max_size = 32768; // 32 KiB
//const uint32_t max_size = 2; // 128 KiB

#endif 


/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
int_handler(int signum, siginfo_t *info, void *ptr);
static void 
usage(char *prog);
static void
terminate(int rc);

static void* 
new_loggp_client(void *conn);
static void 
destroy_loggp_client(void *client);
static void 
handle_client_data(void *endpoint, void *recv_buf, uint32_t recv_len);

static void* 
new_loggp_server(void *conn);
static void 
destroy_loggp_server(void *server);
static void 
handle_server_data(void *endpoint, void *recv_buf, uint32_t recv_len);
static int
loggp_sendn(ep_t *ep);

static int 
cmpfunc_uint64(const void *a, const void *b);

static double 
mean(uint32_t n, double *x);
static double 
sigma(uint32_t n, double *x, double mean);
static void
linreg(uint32_t n, double *x, double *y, double *a, double *b);

static void
poll_cb(EV_P_ ev_idle *w, int revents);

#endif


/* ================================================================== */
/* Global functions */
#if 1

int main(int argc, char* argv[])
{
    struct sigaction act;
    char *out_file = "";
    char host[NI_MAXHOST];
    char port[NI_MAXSERV];
    uint32_t sample_count, size, i;
    int c, rv;
    ep_t *ep;

    /* Set debugger output to STDOUT (temporarily) */
    dbg_stream = stdout;
        
    /* Set handler for SIGINT */
    memset(&act, 0, sizeof(act));
    act.sa_flags = SA_SIGINFO;
    act.sa_sigaction = int_handler;
    sigaction(SIGINT, &act, NULL);
        
    /* Parse command line */
    while (1) {
        static struct option long_options[] = {
            {"client", no_argument, &client, 1},
#ifdef AC_IBV            
            {"ibv",  no_argument, &net_type, AC_NET_IBV},
#endif            
            {"tcp",   no_argument, &net_type, AC_NET_TCP},            
            {0, 0, 0, 0}
        };
        int option_index = 0;
        c = getopt_long (argc, argv, "hs:p:o:l:",
                       long_options, &option_index);
        /* Detect the end of the options. */
        if (c == -1) break;

        switch (c) {
            case 0:
                /* If this option set a flag, do nothing else now. */
                if (long_options[option_index].flag != 0)
                    break;
                info("option %s", long_options[option_index].name);
                if (optarg)
                    info(" with arg %s", optarg);
                info("\n");
                break;

            case 'h':
                usage(argv[0]);
                exit(1);

            case 's':
				strncpy(host, optarg, NI_MAXHOST);
                break;
            
            case 'p':
                strncpy(port, optarg, NI_MAXSERV);
                break;
           
            case 'o':
                out_file = optarg;
                break;
            
            case 'l':
                dbg_stream = fopen(optarg, "w+");
                info("Log file: %s\n", optarg);
                break;

            case '?':
                break;

            default:
                terminate(1);
        }
    }
    
    /* Init event loop */
    loop = EV_DEFAULT;
 
    /* Initialize timer */
    info("Activating timer...");
    HRT_INIT(g_timerfreq);
    info("done\n");
   
    /* Load network module */
    if (AC_NET_TCP == net_type) {
        ac_tcp_reg_module(loop, terminate, 1, NULL);
    }
#ifdef AC_IBV    
    else if (AC_NET_IBV == net_type) {
        ac_ibv_reg_module(loop, terminate, 1, NULL);
    }
#endif  
    info("Loading %s module: %s\n", ac_net_mod->name, ac_net_mod->desc);
    
    if (client) {
        if (strcmp(out_file, "") == 0) {
            info("Error: no output file\n");
            terminate(1);
        }
        out_stream = fopen(out_file, "w+");
        fprintf(out_stream, " s     | prtt(1,0,s) | prtt(n,d,s) | prtt(n,0,s) | o(s) \n");
    }

    
    info_wtime("Let's start...\n\n");

    if (client) {
        if (ep_list != NULL) {
            error("ep list not empty\n");
            terminate(1);
        }
        ep = (ep_t*)malloc(sizeof(ep_t));
        if (!ep) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(ep, 0, sizeof(ep_t));
        loggp_server_t* loggp_server = (loggp_server_t*)
                                        malloc(sizeof(loggp_server_t));
        if (!loggp_server) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(loggp_server, 0, sizeof(loggp_server));
        
        /* Allocate space for regression arrays */
        sample_count = 0;
        for (size = min_size; size <= max_size; size <<= 1) {
            sample_count++;
        }
        loggp_server->x = (double*)malloc(sample_count*sizeof(double));
        if (NULL == loggp_server->x) {
            error("allocating x (%s)\n", strerror(errno));
            terminate(1);
        }
        loggp_server->y = (double*)malloc(sample_count*sizeof(double));
        if (NULL == loggp_server->y) {
            error("allocating y (%s)\n", strerror(errno));
            terminate(1);
        }
        loggp_server->state = PRTT_1_0_S;
        
        ep->data = loggp_server;
        ep->head = &ep_list;
        ac_ep_add(ep);
    
        /* Set endpoint data */
        memcpy(ep->cd.ei.host, host, sizeof host);
        memcpy(ep->cd.ei.port, port, sizeof port);
        ep->cd.rcount = MAX_OUTSTANDING;
        ep->cd.scount = MAX_OUTSTANDING;
        ep->cd.rbuf_len = MAX_BUF_SIZE / MAX_OUTSTANDING;
        ep->cd.sbuf_len = MAX_BUF_SIZE / MAX_OUTSTANDING;
        ep->cd.on_connection = new_loggp_server;
        ep->cd.destroy_ep_data = destroy_loggp_server;
        ep->cd.handle_data = handle_server_data;
    
        /* Create connecting channel, if needed */
        if ((NULL == channel) && (ac_net_mod->create_ch)) {
            channel = ac_net_mod->create_ch();
            if (!channel) {
                error("create_ch\n");
                terminate(1);
            }
        }
    
        /* Connect */
        info_wtime("Connecting to server\n");
        rv = ac_net_mod->iconnect(ep, channel);
        if (rv) {
            error("iconnect\n");
            terminate(1);
        }
    }
    else {
        /* Listen for incoming connection */
        conn_data_t conn_data = {
            .rcount = MAX_OUTSTANDING,
            .scount = MAX_OUTSTANDING,
            .rbuf_len = MAX_BUF_SIZE / MAX_OUTSTANDING,
            .sbuf_len = MAX_BUF_SIZE / MAX_OUTSTANDING,
            
            .on_connection = new_loggp_client,
            .destroy_ep_data = destroy_loggp_client,
            .handle_data = handle_client_data,
        };
        memcpy(conn_data.ei.port, port, sizeof port);
        channel = ac_net_mod->ilisten(&conn_data);
        if (NULL == channel) {
            error("ilisten\n");
            terminate(1);
        }
    }
    
    /* Init the poll event */
    ev_idle_init(&w_poll, poll_cb);
    ev_set_priority(&w_poll, EV_MAXPRI);
    ev_idle_start(loop, &w_poll);
    
    /* Start loop */
    ev_run(loop, 0);

    return 0;
}

#endif


/* ================================================================== */
/* Local functions */
#if 1

static void 
int_handler(int signum, siginfo_t *info, void *ptr)
{
    info_wtime("[%s:%s:%d] Received signal %d\n", 
           __FILE__, __func__, __LINE__, signum);
    info("Signal originates from process %lu\n",
            (unsigned long)info->si_pid);
    recv_sigint = 1;
}

static void 
usage(char *prog)
{
    printf("Usage: %s [OPTIONS]\n"
            "OPTIONS:\n"
#ifdef AC_IBV            
            "\t--tcp | --ibv | --rdma   server-interconnection type\n"
#else
            "\t--tcp                    server-interconnection type\n"
#endif            
            "\t--client             client flag\n"
            "\t-s <host>            server hostname\n"
            "\t-p <port>            server listening port\n"
            "\t-l <filename>     	logging file\n"
            "\t-o <filename>        output file\n",
            prog);
}

static void
terminate(int rc) 
{
    ep_t *ep;
    
    info("\nShutting down\n");

    /* Close poll watcher */
    ev_idle_stop(loop, &w_poll);
    
    /* Free list of clients */
    info_wtime("Disconnecting remote endpoint\n");
    while (NULL != (ep = ep_list)) {
        ep_list = ep->next;
        ac_ep_destroy(ep);
    } 
    
    if (ac_net_mod->wait_for_disconnects) {
        info_wtime("Waiting for endpoint disconnections\n");
        ac_net_mod->wait_for_disconnects(channel);
    }
    
    ac_net_mod->destroy_ch(channel);
    channel = NULL;
    
    if (NULL != out_stream) {
        fclose(out_stream);
        out_stream = NULL;
    }

    info_wtime("Bye bye\n\n");
    if ((stdout != dbg_stream) && (NULL != dbg_stream)) {
        fclose(dbg_stream);
        dbg_stream = NULL;
    }
    exit(rc);
}

static void* 
new_loggp_client(void *conn)
{
    info_wtime("Client connected\n");
    
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = (ep_t*)malloc(sizeof(ep_t));
    if (NULL == ep) {
        error("malloc (%s)\n", strerror(errno));
        return NULL;
    }
    memset(ep, 0, sizeof(ep_t));
    ep->conn = conn;
    conn_ctx->ep = ep;
    conn_ctx->buffering = 1;
    ep->connected = 1;
    
    ep->data = malloc(sizeof(loggp_client_t));
    if (NULL == ep->data) {
        error("malloc (%s)\n", strerror(errno));
        free(ep);
        return NULL;
    }
    loggp_client_t *loggp_client = (loggp_client_t*)ep->data;
    memset(loggp_client, 0, sizeof(loggp_client_t));
    loggp_client->state = PRTT_1_0_S;
    loggp_client->byte_count = 0;
    loggp_client->measure_count = 0;
    loggp_client->size = min_size;
    loggp_client->n = 1;

    ep->head = &ep_list;
    ac_ep_add(ep);    
    return ep;
}

static void 
destroy_loggp_client(void *client)
{
    loggp_client_t *loggp_client = (loggp_client_t*)client;
    if (NULL == client) return;
    
    free(loggp_client);
}

static void 
handle_client_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    int rv;
    uint32_t len;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        terminate(1);
    }
    loggp_client_t *loggp_client = (loggp_client_t*)ep->data;
    if (!loggp_client) {
        error("loggp_client is NULL\n");
        terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        terminate(1);
    }

    
    while (recv_len != 0) {
        len = loggp_client->size - loggp_client->byte_count;
        if (recv_len < len) {
            /* partially */
            loggp_client->byte_count += recv_len;
            return;
        }
        /* received message completely */
        recv_len -= len;
        loggp_client->byte_count = 0;
        loggp_client->n--;
        if (loggp_client->n) 
            continue; 
 
        /* Done receiving from client; send reply */
        uint32_t bytes = sizeof(shared_buf_t) + loggp_client->size;
        shared_buf_t *sh_buf = (shared_buf_t*)malloc(bytes);
        if (NULL == sh_buf) {
            error("malloc (%s)\n", strerror(errno));
            terminate(1);
        }
        memset(sh_buf, 0, bytes);
        sh_buf->len = bytes - sizeof(shared_buf_t);
        memset(sh_buf->buf, 'x', loggp_client->size);
        
        /* Send the message (asynch) */
        rv = ac_net_mod->isend(ep, sh_buf);
        if (rv) {
            error("isend\n");
            terminate(1);
        }
        if (!sh_buf->shared_count) {
            free(sh_buf);
            sh_buf = NULL;
        }

        loggp_client->measure_count++;
        if (loggp_client->measure_count < MEASURE_COUNT) {
            switch (loggp_client->state) {
            case PRTT_1_0_S:
                loggp_client->n = 1;
                break;
            case PRTT_N_D_S:
                loggp_client->n = N;
                 break;
            case PRTT_N_0_S:
                loggp_client->n = N;
                break;
            }
            continue;
        }
        
        /* Done with this PRTT */
        loggp_client->measure_count = 0;
        
        switch (loggp_client->state) {
        case PRTT_1_0_S:
            loggp_client->n = N;
            loggp_client->state = PRTT_N_D_S;
            break;
        case PRTT_N_D_S:
            loggp_client->n = N;
            loggp_client->state = PRTT_N_0_S;
            break;
        case PRTT_N_0_S:
            /* Increase size */
            loggp_client->size <<= 1;
            loggp_client->n = 1;
            loggp_client->state = PRTT_1_0_S;
            if (loggp_client->size > max_size) {
                info_wtime("Done; waiting for client\n");
                return;
            }
            break;
        }
    }
}

static void* 
new_loggp_server(void *conn)
{
    int rv;
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = conn_ctx->ep;
    loggp_server_t *loggp_server = (loggp_server_t*)ep->data;

    info_wtime("Connected to %s:%s\n", ep->cd.ei.host, ep->cd.ei.port);
    conn_ctx->buffering = 1;
    ep->connected = 1;
        
    /* Start sending messages: loggp_prtt(1, 0, size);*/
    loggp_server->size = min_size;
    loggp_server->n = 1;
    loggp_server->measure_count = 0;
    loggp_server->state = PRTT_1_0_S;
    loggp_server->byte_count = 0;
    loggp_server->delay = 0;
    loggp_server->i = 0;
    
    rv = loggp_sendn(ep);
    if (rv) {
        error("loggp_sendn\n");
        return NULL;
    }
    
    return ep;
}

static void 
destroy_loggp_server(void *server)
{
    loggp_server_t *loggp_server = (loggp_server_t*)server;
    if (NULL == server) return;
    
    if (loggp_server->x) {
        free(loggp_server->x);
        loggp_server->x = NULL;
    }
    
    if (loggp_server->y) {
        free(loggp_server->y);
        loggp_server->y = NULL;
    }
    
    free(loggp_server);
}

void handle_server_data(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    int rv;
    double o, g, G;
    uint32_t sample_count, size, len;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        terminate(1);
    }
    loggp_server_t *loggp_server = (loggp_server_t*)ep->data;
    if (!loggp_server) {
        error("loggp_server is NULL\n");
        terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        terminate(1);
    }
       
    while (recv_len != 0) {
        len = loggp_server->size - loggp_server->byte_count;
        if (recv_len < len) {
            /* partially */
            loggp_server->byte_count += recv_len;
            return;
        }
        /* received reply completely */
        recv_len -= len;
        loggp_server->byte_count = 0;
        HRT_GET_TIMESTAMP(loggp_server->t2);
        HRT_GET_ELAPSED_TICKS(loggp_server->t1, loggp_server->t2, 
                    &(loggp_server->ticks[loggp_server->measure_count]));
        loggp_server->measure_count++;
        /* Received reply from server */
        if (loggp_server->measure_count == MEASURE_COUNT) 
            goto experiment_completed;

        /* Repeat experiment */
        rv = loggp_sendn(ep);
        if (rv) {
            error("loggp_sendn\n");
            terminate(1);
        }
        break;

experiment_completed:        
        /* Gather statistical data */
        qsort(loggp_server->ticks, MEASURE_COUNT, sizeof(uint64_t), cmpfunc_uint64);
        int median_index = MEASURE_COUNT/2;
        double usecs = HRT_GET_USEC(loggp_server->ticks[median_index]);
#if 0        
        int min_index = 0;
        int max_index = MEASURE_COUNT-1;
        int p1_index = MEASURE_COUNT/100;
        int q1_index = MEASURE_COUNT/4;
        int q3_index = 3*MEASURE_COUNT/4;
        int p99_index = 99*MEASURE_COUNT/100;
        info("   %9.3lf-{%9.3lf-[%9.3lf-%9.3lf-%9.3lf]-%9.3lf}-%9.3lf\n", 
                  HRT_GET_USEC(loggp_server->ticks[min_index]),
                  HRT_GET_USEC(loggp_server->ticks[p1_index]),
                  HRT_GET_USEC(loggp_server->ticks[q1_index]),
                  HRT_GET_USEC(loggp_server->ticks[median_index]),
                  HRT_GET_USEC(loggp_server->ticks[q3_index]),
                  HRT_GET_USEC(loggp_server->ticks[p99_index]),
                  HRT_GET_USEC(loggp_server->ticks[max_index]));
#endif
        loggp_server->measure_count = 0;
        switch (loggp_server->state) {
        case PRTT_1_0_S:
            loggp_server->prtt_1_0_s = usecs;
            /* Start loggp_prtt(N, prtt_1_0_s, size); */
            loggp_server->n = N;
            loggp_server->delay = loggp_server->prtt_1_0_s;
            rv = loggp_sendn(ep);
            if (rv) {
                error("loggp_sendn\n");
                terminate(1);
            }
            loggp_server->state = PRTT_N_D_S;
            break;
        case PRTT_N_D_S:
            loggp_server->prtt_n_d_s = usecs;
            /* Start loggp_prtt(N, 0, size); */
            loggp_server->n = N;
            loggp_server->delay = 0;
            rv = loggp_sendn(ep);
            if (rv) {
                error("loggp_sendn\n");
                terminate(1);
            }
            loggp_server->state = PRTT_N_0_S;
            break;
        case PRTT_N_0_S:
            loggp_server->prtt_n_0_s = usecs;
            /* Compute LogGP parameters */
            o = (loggp_server->prtt_n_d_s - loggp_server->prtt_1_0_s) 
                / (N-1) - loggp_server->prtt_1_0_s;
            if (loggp_server->size == min_size) {
                loggp_server->L = loggp_server->prtt_1_0_s / 2;
            }
            loggp_server->x[loggp_server->i] = loggp_server->size - 1;
            loggp_server->y[loggp_server->i] = 
                (loggp_server->prtt_n_0_s - loggp_server->prtt_1_0_s) 
                / (N-1);
            loggp_server->i++;
            fprintf(out_stream, "%6"PRIu32" | %11.3lf | %11.3lf | %11.3lf | %9.3lf \n", 
                loggp_server->size, loggp_server->prtt_1_0_s, 
                loggp_server->prtt_n_d_s, loggp_server->prtt_n_0_s, o);
            //info("\n");
            
            /* Increase size */
            loggp_server->size <<= 1;
            if (loggp_server->size > max_size) {
                /* Solve y = g + (s-1)G */
                sample_count = 0;
                for (size = min_size; size <= max_size; size <<= 1) {
                    sample_count++;
                }
                if (sample_count > 8) {
                    linreg(sample_count-8, loggp_server->x+8, 
                            loggp_server->y+8, &g, &G);
                    fprintf(out_stream, "L=%9.3lf; G=%9.3lf; g=%9.3lf\n", 
                                loggp_server->L, G, g);
                }
                terminate(0);
            }
            /* Start loggp_prtt(1, 0, size); */
            loggp_server->n = 1;
            loggp_server->delay = 0;
            rv = loggp_sendn(ep);
            if (rv) {
                error("loggp_sendn\n");
                terminate(1);
            }
            loggp_server->state = PRTT_1_0_S;
            break;
        }
    }
}

static int
loggp_sendn(ep_t *ep)
{    
    int rv;
    uint32_t i;
    shared_buf_t **sh_buf;
    
    loggp_server_t *loggp_server = (loggp_server_t*)ep->data;
    if (!loggp_server) {
        error("loggp_server is NULL\n");
        return 1;
    }
    
    //info_wtime("calling loggp_prtt(%"PRIu32", %lf, %"PRIu32")\n", 
    //        loggp_server->n, loggp_server->delay, loggp_server->size);
            
    sh_buf = (shared_buf_t**)malloc(loggp_server->n*sizeof(shared_buf_t*));
    if (NULL == sh_buf) {
        error("malloc (%s)\n", strerror(errno));
        return 1;
    }
    uint32_t bytes = sizeof(shared_buf_t) + loggp_server->size;
    for (i = 0; i < loggp_server->n; i++) {
        sh_buf[i] = (shared_buf_t*)malloc(bytes);
        if (NULL == sh_buf[i]) {
            error("malloc (%s)\n", strerror(errno));
            goto exit_with_error;
        }
        memset(sh_buf[i], 0, bytes);
        sh_buf[i]->len = bytes - sizeof(shared_buf_t);
        memset(sh_buf[i]->buf, 'x', loggp_server->size);
    }
    
    HRT_GET_TIMESTAMP(loggp_server->t1);
        
    /* Send the message (asynch) */
    rv = ac_net_mod->isend(ep, sh_buf[0]);
    if (rv) {
        error("isend\n");
        return 1;
    }
    if (!sh_buf[0]->shared_count) {
        free(sh_buf[0]);
        sh_buf[0] = NULL;
    }
    
    for (i = 1; i < loggp_server->n; i++) {
        if (loggp_server->delay > 0) usecs_wait(loggp_server->delay);
        /* Send the message (asynch) */
        rv = ac_net_mod->isend(ep, sh_buf[i]);
        if (rv) {
            error("isend\n");
            return 1;
        }
        if (!sh_buf[i]->shared_count) {
            free(sh_buf[i]);
            sh_buf[i] = NULL;
        }
    }
    return 0;
    
exit_with_error:
    for (i = 0; i < loggp_server->n; i++) {
        if (sh_buf[i]) {
            free(sh_buf[i]);
        }
        free(sh_buf);
    }
    return 1;
}

static int 
cmpfunc_uint64(const void *a, const void *b)
{
    return ( *(uint64_t*)a - *(uint64_t*)b );
}

/**
 * Compute mean
 */
static double 
mean(uint32_t n, double *x)
{
    double sum = 0;
    uint32_t i;
    for (i = 0; i < n; i++) {
        sum += x[i];
    }
    return (sum/n);
}

/**
 * Compute standard deviation
 */
static double 
sigma(uint32_t n, double *x, double mean)
{
    double sigma = 0, d;
    uint32_t i;
    for (i = 0; i < n; i++) {
        d = x[i] - mean;
        sigma += d*d;
    }
    sigma /= n;
    return sqrt(sigma);
}

/**
 * Linear regression: y = a + by
 */
static void
linreg(uint32_t n, double *x, double *y, double *a, double *b)
{
    double mean_x, mean_y, sigma_x, sigma_y, r = 0;
    uint32_t i;


    mean_x = mean(n, x);
    mean_y = mean(n, y);
    sigma_x = sigma(n, x, mean_x);
    sigma_y = sigma(n, y, mean_y);

    /* Compute Pearson correlation coefficient */
    for (i = 0; i < n; i++) {
        r += (x[i]-mean_x)*(y[i]-mean_y);
    }
    r /= (n-1)*sigma_x*sigma_y;

    /* Compute coeficients */
    *b = r * sigma_y / sigma_x;
    *a = mean_y - (*b)*mean_x;
}

static void
poll_cb(EV_P_ ev_idle *w, int revents)
{
    int rv;
    ep_t *ep;
    
    if (recv_sigint) {
        terminate(0);
    }

    /* Poll for connections */
    if (ac_net_mod->poll_ch) {
        rv = ac_net_mod->poll_ch(channel);
        if (rv) {
            error("poll_ch\n");
            terminate(1);
        }
    }
    
    /* Poll for incoming data */
    if (ac_net_mod->poll_recv) {
        ep = ep_list;
        while (NULL != ep) {
            if (!ep->connected) {
                ep = ep->next;
                continue;
            }
            rv = ac_net_mod->poll_recv(ep);
            if (rv) {
                error("poll_recv\n");
                terminate(1);
            }            
            ep = ep->next;
        }
    }
    
    /* Poll completion of send operations */
    if (ac_net_mod->poll_send) {
        ep = ep_list;
        while (NULL != ep) {
            if (!ep->connected) {
                ep = ep->next;
                continue;
            }
            rv = ac_net_mod->poll_send(ep);
            if (-1 == rv) {
                error("poll_send\n");
                terminate(1);
            }            
            ep = ep->next;
        }
    }
}

#endif
