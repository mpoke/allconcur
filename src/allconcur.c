/**   
 * AllConcur
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

/* Bug in gcc prevents from using CPP_DEMANGLE in pure "C" */
#if !defined(__cplusplus) && !defined(NO_CPP_DEMANGLE)
#define NO_CPP_DEMANGLE
#endif
 
#include <debug.h>
#include <stdlib.h>
#include <unistd.h>
#define __USE_GNU
#include <signal.h>
#include <ucontext.h>

#include <dlfcn.h>
#ifndef NO_CPP_DEMANGLE
#include <cxxabi.h>
#ifdef __cplusplus
using __cxxabiv1::__cxa_demangle;
#endif
#endif

#ifdef HAS_ULSLIB
#include "uls/logger.h"
#define sigsegv_outp(x)         sigsegv_outp(,gx)
#else
#define sigsegv_outp(x, ...)    fprintf(stderr, x "\n", ##__VA_ARGS__)
#endif

#if defined(REG_RIP)
# define SIGSEGV_STACK_IA64
# define REGFORMAT "%016lx"
#elif defined(REG_EIP)
# define SIGSEGV_STACK_X86
# define REGFORMAT "%08x"
#else
# define SIGSEGV_STACK_GENERIC
# define REGFORMAT "%x"
#endif

#include <sys/types.h>
#include <sys/wait.h>
#include <sys/prctl.h>
#include <getopt.h>

#include <net/tcp/include/ac_tcp.h>
#include <net/ibv/include/ac_ibv.h>

#include <ctrl_sm.h>
#include <ac_init.h>
#include <ac_algorithm.h>
#include <ac_fd.h>
#include <client_listener.h>
#include <messages.h>
#include <allconcur.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define READ_REPLY      1
#define READ_SNAPSHOT   2

#endif

/* ================================================================== */
/* Global variables */
#if 1

FILE *dbg_stream;
FILE *fd_stream;
data_t data;

int timer = 0;
int join;
#ifdef AC_IBV            
int net_type = AC_NET_IBV;
#else
int net_type = AC_NET_TCP;
#endif
#ifdef BENCHMARK 
int bench_type = AC_BENCH_REQ;
#endif 
unsigned long long g_timerfreq;

tuple_t *tuple_queue;

ac_net_module_t *ac_net_mod;

int recv_sigint = 0;

int fd_thread_created = 0;
int c_listener_created = 0;

uint64_t poll_count;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
usage(char *prog);
static void 
int_handler(int signum, siginfo_t *info, void *ptr);
static void 
segv_handler(int signum, siginfo_t *info, void *ptr);

static void 
signal_segv(int signum, siginfo_t* info, void*ptr);

static int 
parse_config(char *filename);
static void
init_allconcur(uint32_t n, uint32_t rnines);
static int 
join_allconcur(char *host, char *port);
static void* 
send_join_request(void *conn);
static void 
handle_join_reply(void *endpoint, void *recv_buf, uint32_t recv_len);

/* Callbacks */
static void
poll_cb(EV_P_ ev_idle *w, int revents);

#endif

/* ================================================================== */
/* Global functions */
#if 1

int main(int argc, char* argv[])
{
    int c, rv, i;
    char *config_file="";
    uint32_t n = 6, rnines = 6;
    struct sigaction act;
    char host[NI_MAXHOST];
    char port[NI_MAXSERV];

    /* Set debugger output to STDOUT (temporarily) */
    dbg_stream = stdout;
    fd_stream = stdout;
        
    /* Set handler for SIGINT */
    memset(&act, 0, sizeof(act));
    act.sa_flags = SA_SIGINFO;
    act.sa_sigaction = int_handler;
    sigaction(SIGINT, &act, NULL);
    
    /* Set handler for SIGSEGV */
    memset(&act, 0, sizeof(act));
    act.sa_flags = SA_SIGINFO;
    //act.sa_sigaction = segv_handler;
    act.sa_sigaction = signal_segv;
    sigaction(SIGSEGV, &act, NULL);
        
    /* Parse command line */
    while (1) {
        static struct option long_options[] = {
            /* These options set the type of the SM */
#ifdef AC_IBV            
            {"ibv",  no_argument, &net_type, AC_NET_IBV},
#endif            
            {"tcp",   no_argument, &net_type, AC_NET_TCP},
            /* Flag for timer */
            {"timer", no_argument, &timer, 1},
            /* Flag for joining */
            {"join", no_argument, &join, 1},
#ifdef BENCHMARK            
            {"latency", no_argument, &bench_type, AC_BENCH_LAT},
            {"throughput",  no_argument, &bench_type, AC_BENCH_THRP},
            {"failure",   no_argument, &bench_type, AC_BENCH_FAIL},
#endif
            {0, 0, 0, 0}
        };
        int option_index = 0;
        c = getopt_long (argc, argv, "hn:c:r:s:p:",
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
                
            case 'n':
				n = (uint32_t)atoi(optarg);
                break;
            
            case 'r':
                rnines = (uint32_t)atoi(optarg);
                break;
                
            case 'c':
                config_file = optarg;
                break;
            
            case 's':
				strncpy(host, optarg, NI_MAXHOST);
                break;
            
            case 'p':
                strncpy(port, optarg, NI_MAXSERV);
                break;

            case '?':
                break;

            default:
                exit(1);
        }
    }
    if (strcmp(config_file, "") == 0) {
        error("no configuration file\n");
        exit(1);
    }

    /* Initialize data */
    memset(&data, 0, sizeof(data));

    /* Parse configuration file */
    rv = parse_config(config_file);
    if (0 != rv) {
        error("parse_config\n");
        terminate(1);
    }
#ifdef BENCHMARK    
    /* Set outstanding sends (per connection) to the number of servers 
       Note: these parameters are relevant for IBV */
    data.outstanding = n;
    data.max_buf_size = (data.req_size * data.max_batching + sizeof(message_t))*data.outstanding;
#endif    
    
    /* Init event loop */
    data.loop = EV_DEFAULT;
 
    if (timer) {
        /* Initialize timer */
        HRT_TIMESTAMP_T t1, t2;
        uint64_t ticks;
        info_wtime("Initializing timer...");
        if (!join) {
            HRT_GET_TIMESTAMP(t1);
        }
        
        HRT_INIT(g_timerfreq);
        
        if (!join) {
            /* Wait 20 seconds for timer initialization */
            HRT_GET_TIMESTAMP(t2);
            HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
            usecs_wait(20*1e6 - HRT_GET_USEC(ticks));
        }
        info("done!\n");
    }
   
    /* Load network module */
    if (AC_NET_TCP == net_type) {
        ac_tcp_reg_module(data.loop, terminate, timer, check_termination);
    }
#ifdef AC_IBV    
    else if (AC_NET_IBV == net_type) {
        ac_ibv_reg_module(data.loop, terminate, timer, check_termination);
        info("Set %"PRIu32" (%"PRIu32"-byte) buffers (per connection)\n", data.outstanding, data.max_buf_size/data.outstanding);
    }
#endif  
    info("Loading %s module: %s\n", ac_net_mod->name, ac_net_mod->desc);
    
    if (join) {
        if (0 != join_allconcur(host, port)) {
            error("join_allconcur\n");
            terminate(1);
        }
    }
    else {
        init_allconcur(n, rnines);
    }

    /* Init the poll event */
    ev_idle_init(&data.w_poll, poll_cb);
    ev_set_priority(&data.w_poll, EV_MAXPRI);
    ev_idle_start(data.loop, &data.w_poll);
    
    /* Start loop */
    ev_run(data.loop, 0);

    return 0;
}



void terminate(int rc) 
{
    info("\nShutting down\n");

    /* Close poll watcher */
    ev_idle_stop(data.loop, &data.w_poll);

    if (!join) {
        pthread_mutex_unlock(&data.quit_mutex);
        if (c_listener_created) {
            pthread_join(data.c_listener, NULL);
            pthread_mutex_destroy(&data.clt_mutex);
        }
        if (fd_thread_created) {
            pthread_join(data.fd_thread, NULL);
            pthread_mutex_destroy(&data.quit_mutex);
            pthread_mutex_destroy(&data.fd.next_mutex);
            pthread_cond_destroy(&data.fd.cond);
            pthread_mutex_destroy(&data.fd.prev_mutex);
        }
    
#ifdef BENCHMARK    
        benchmark_destroy();
#endif 
 
        info_wtime("Tear down datagram transfer ...");
        if (data.fd.ud.ud_info.endpoint) {
            free(data.fd.ud.ud_info.endpoint);
            data.fd.ud.ud_info.endpoint = NULL;
        }
        ac_net_mod->disconnect(data.fd.ud.conn);
        info("done\n");

        ac_destroy();
    
        /* Free list of prematurely received messages */
        destroy_message_queue(&premature_msgs);
    
        ac_net_mod->destroy_ch(data.prev_srv_ch);
        data.prev_srv_ch = NULL;
        
        ac_net_mod->destroy_ch(data.client_ch);
        data.client_ch = NULL;
    }

    ac_net_mod->destroy_ch(data.next_srv_ch);
    data.next_srv_ch = NULL;
    
    info_wtime("Bye bye\n\n");
    if ((stdout != fd_stream) && (NULL != fd_stream) && (dbg_stream != fd_stream)) {
        fclose(fd_stream);
        fd_stream = NULL;
    }
    if ((stdout != dbg_stream) && (NULL != dbg_stream)) {
        fclose(dbg_stream);
        dbg_stream = NULL;
    }
    exit(rc);
}

/**
 * Send a request to connect to the server with ID sid
 */
int connect_to(uint32_t sid)
{
    int rv;
    srv_t *srv = &data.vertex_to_srv_map[sid];
    ep_t *ep, *prev = NULL;
    next_srv_t *next_srv = NULL;
    
    if (server_is_failed(sid)) {
        /* Server failed in a previous round */
        return 0;
    }
    if (server_failed_crt_round(sid)) {
        /* Received failure notification in this round */
        return 0;
    }
    
    ep = data.next_srv_list;
    while (NULL != ep) {
        next_srv_t *next_srv = (next_srv_t*)ep->data;
        if (sid == next_srv->sid) break;
        prev = ep;
        ep = ep->next;
    }
    if (ep == NULL) {
        /* New successor */
        ep = (ep_t*)malloc(sizeof(ep_t));
        if (!ep) {
            error("malloc (%s)\n", strerror(errno));
            return 1;
        }
        memset(ep, 0, sizeof(ep_t));
        next_srv = (next_srv_t*)malloc(sizeof(next_srv_t));
        if (!next_srv) {
            error("malloc (%s)\n", strerror(errno));
            return 1;
        }
        memset(next_srv, 0, sizeof(next_srv_t));
        next_srv->sid = sid;
        ep->data = next_srv;
        
        ep->head = &data.next_srv_list;
        ac_ep_add(ep);
    }
    if (ep->connected) {
        /* Already connected */
        return 0;
    }
        
    /* Set endpoint data */
    memcpy(ep->cd.ei.host, srv->srv_value->ni.host, sizeof srv->srv_value->ni.host);
    memcpy(ep->cd.ei.port, srv->srv_value->ni.ac_port, sizeof srv->srv_value->ni.ac_port);
    ep->cd.rcount = data.outstanding;
    ep->cd.scount = data.outstanding;
    ep->cd.rbuf_len = 64;
    ep->cd.sbuf_len = data.max_buf_size / data.outstanding;
    ep->cd.on_connection = new_successor;
    ep->cd.destroy_ep_data = ac_destroy_next_srv;
    ep->cd.handle_data = handle_next_data;
    
    /* Create connecting channel, if needed */
    if ((NULL == data.next_srv_ch) && (ac_net_mod->create_ch)) {
        data.next_srv_ch = ac_net_mod->create_ch();
        if (!data.next_srv_ch) {
            error("create_ch\n");
            return 1;
        }
    }
    
    /* Connect */
    info_wtime("Connecting to p%"PRIu32"\n", sid);
    rv = ac_net_mod->iconnect(ep, data.next_srv_ch);
    if (rv) {
        error("iconnect\n");
        return 1;
    }
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
signal_segv(int signum, siginfo_t* info, void*ptr) {
    static const char *si_codes[3] = {"", "SEGV_MAPERR", "SEGV_ACCERR"};

    int i, f = 0;
    ucontext_t *ucontext = (ucontext_t*)ptr;
    Dl_info dlinfo;
    void **bp = 0;
    void *ip = 0;

    sigsegv_outp("Segmentation Fault!");
    sigsegv_outp("info.si_signo = %d", signum);
    sigsegv_outp("info.si_errno = %d", info->si_errno);
    sigsegv_outp("info.si_code  = %d (%s)", info->si_code, si_codes[info->si_code]);
    sigsegv_outp("info.si_addr  = %p", info->si_addr);
    for(i = 0; i < NGREG; i++)
        sigsegv_outp("reg[%02d]       = 0x" REGFORMAT, i, ucontext->uc_mcontext.gregs[i]);

#ifndef SIGSEGV_NOSTACK
#if defined(SIGSEGV_STACK_IA64) || defined(SIGSEGV_STACK_X86)
#if defined(SIGSEGV_STACK_IA64)
    ip = (void*)ucontext->uc_mcontext.gregs[REG_RIP];
    bp = (void**)ucontext->uc_mcontext.gregs[REG_RBP];
#elif defined(SIGSEGV_STACK_X86)
    ip = (void*)ucontext->uc_mcontext.gregs[REG_EIP];
    bp = (void**)ucontext->uc_mcontext.gregs[REG_EBP];
#endif

    sigsegv_outp("Stack trace:");
    while(bp && ip) {
        if(!dladdr(ip, &dlinfo))
            break;

        const char *symname = dlinfo.dli_sname;

#ifndef NO_CPP_DEMANGLE
        int status;
        char * tmp = __cxa_demangle(symname, NULL, 0, &status);

        if (status == 0 && tmp)
            symname = tmp;
#endif

        sigsegv_outp("% 2d: %p <%s+%lu> (%s)",
                 ++f,
                 ip,
                 symname,
                 (unsigned long)ip - (unsigned long)dlinfo.dli_saddr,
                 dlinfo.dli_fname);

#ifndef NO_CPP_DEMANGLE
        if (tmp)
            free(tmp);
#endif

        if(dlinfo.dli_sname && !strcmp(dlinfo.dli_sname, "main"))
            break;

        ip = bp[1];
        bp = (void**)bp[0];
    }
#else
    sigsegv_outp("Stack trace (non-dedicated):");
    sz = backtrace(bt, 20);
    strings = backtrace_symbols(bt, sz);
    for(i = 0; i < sz; ++i)
        sigsegv_outp("%s", strings[i]);
#endif
    sigsegv_outp("End of stack trace.");
#else
    sigsegv_outp("Not printing stack strace.");
#endif
    _exit (-1);
}



static void 
segv_handler(int signum, siginfo_t *info, void *ptr)
{
    ucontext_t *uc = (ucontext_t *)ptr;

    info_wtime("[%s:%s:%d] Received signal %d\n", 
           __FILE__, __func__, __LINE__, signum);
    info("   SEGV originates from process %lu at %p\n",
            (unsigned long)info->si_pid, info->si_addr);
    info("   ip: %x\n", uc->uc_mcontext.gregs[REG_RIP]);
    exit(1);
}

static void 
usage(char *prog)
{
    printf("Usage: %s [OPTIONS]\n"
            "OPTIONS:\n"
            "\t-c <config-file>         configuration file\n"
#ifdef AC_IBV            
            "\t[--tcp | --ibv]          server-interconnection type (dafault=ibv)\n"
#else
            "\t[--tcp]                  server-interconnection type (default=tcp)\n"
#endif            
            "\t[-n <size>]              number of nodes (default=6)\n"
            "\t[-r <k-nines>]           required reliability (default=6)\n"
            "\t[--join]                 join group a servers\n"
            "\t   -s <hostname>         [join] server's hostname\n"
            "\t   -p <port>             [join] server's port\n"
            "\t[--timer]                get runtime estimates (default no)\n"
            "\t[--latency]              run latency benchmark\n"
            "\t[--throughput]           run peak throughput benchmark\n"
            "\t[--failure]              run failure benchmark\n",
            prog);
}

static int 
parse_config(char *filename)
{
    ep_id_t ei;
    uint32_t i, rv;
    char line[LINE_MAX];
    char *word;

    data.outstanding = MAX_OUTSTANDING;
    data.max_buf_size = MAX_BUF_SIZE;
#ifdef BENCHMARK
    data.req_size = 64;
    data.max_batching = 2048;
    data.t_req = 1.;
    data.t_req_err = 0.1;
#endif 
    
    FILE *cfg = NULL;
    cfg = fopen(filename, "r");
    if (NULL == cfg) {
        info("Error: fopen (%s)\n", strerror(errno));
        return 1;
    }
    while (fgets(line, LINE_MAX, cfg)) {
        if (line[0] == '#') continue;
        if (line[0] == '\n') continue;
        /* Remove trailing newline */
        line[strcspn(line, "\r\n")] = 0;

        /* Parse line */
        word = strtok (line," \t\r\n");
        if (strcmp(word, "log_file") == 0) {
            word = strtok(NULL, " \t\r\n");
            dbg_stream = fopen(word, "w+");
            info("Log file: %s\n", word);
        }
        if (strcmp(word, "fd_file") == 0) {
            word = strtok(NULL, " \t\r\n");
            fd_stream = fopen(word, "w+");
            info("FD log file: %s\n", word);
        }
        else if (strcmp(word, "server_file") == 0) {
            if (!join) {
                word = strtok (NULL, " \t\r\n");
                info("Server file: %s\n", word);
                data.srv_file = strdup(word);
            }
        }
        else if (strcmp(word, "self") == 0) {
            /* hostname */
            word = strtok (NULL, " \t\r\n");
            strcpy(data.self_ni.host, word);
            /* allconcur port */
            word = strtok (NULL, " \t\r\n");
            strcpy(data.self_ni.ac_port, word);
            /* FD port */
            word = strtok (NULL, " \t\r\n");
            strcpy(data.self_ni.fd_port, word);
            /* clt_port */
            word = strtok (NULL, " \t\r\n");
            strcpy(data.clt_port, word);
        }
        else if (strcmp(word, "timeout") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.fd.timeout = (double)atof(word);
            info("Timeout: %lf\n", data.fd.timeout);
        }
        else if (strcmp(word, "warmup_period") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.fd.warmup = (double)atof(word);
            info("Warm-up period: %lf\n", data.fd.warmup);
        }
        else if (strcmp(word, "hb_period") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.fd.hb_period = (double)atof(word);
            info("HB Period: %lf\n", data.fd.hb_period);
        }
        else if (strcmp(word, "outstanding") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.outstanding = (uint32_t)atoi(word);
            info("Maximum outstanding sends: %"PRIu32"\n", data.outstanding);
        }
        else if (strcmp(word, "max_buf_size") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.max_buf_size = (uint32_t)atoi(word);
            info("Maximum network buffer size: %"PRIu32"\n", data.max_buf_size);
        }
#ifdef BENCHMARK
#ifdef MSG_DELAY        
        else if (strcmp(word, "delay-file") == 0) {
            word = strtok(NULL, " \t\r\n");
            data.delay_stream = fopen(word, "w+");
            info("File with message delay times: %s\n", word);
        }
#endif        
        else if (strcmp(word, "t-round-file") == 0) {
            word = strtok(NULL, " \t\r\n");
            data.t_round_stream = fopen(word, "w+");
            info("File with round times: %s\n", word);
        }
        else if (strcmp(word, "t-request-file") == 0) {
            word = strtok(NULL, " \t\r\n");
            data.t_request_stream = fopen(word, "w+");
            info("File with request times: %s\n", word);
        }
        else if (strcmp(word, "throughput-file") == 0) {
            word = strtok(NULL, " \t\r\n");
            data.throughput_stream = fopen(word, "w+");
            info("Throughput file: %s\n", word);
        }  
        else if (strcmp(word, "req_period") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.t_req = atof(word);
            word = strtok (NULL, " \t\r\n");
            data.t_req_err = atof(word);
            info("Request generating period (milisecond): %lf +/- %lf\n", 
                        data.t_req, data.t_req_err);
        }
        else if (strcmp(word, "req_size") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.req_size = (uint32_t)atoi(word);
            info("Request size (bytes): %"PRIu32"\n", data.req_size);
        }
        else if (strcmp(word, "max_batching") == 0) {
            word = strtok (NULL, " \t\r\n");
            data.max_batching = (uint32_t)atoi(word);
            info("Maximum batching factor (#requests/msg): %"PRIu32"\n", data.max_batching);
        }
#endif        
    }
    
    if (fd_stream == stdout) {
        fd_stream = dbg_stream;
    }

    fclose(cfg);
    return 0;
}

static void
init_allconcur(uint32_t n, uint32_t rnines) 
{
    char filename[NAME_MAX];
    char line[LINE_MAX];
    char *word;
    srv_t *srv;
    uint32_t sid;
    int rv, i;

    rv = ac_init(n, rnines);
    if (0 != rv) {
        error("ac_init\n");
        terminate(1);
    }
    
    info_wtime("Let's start...\n\n");
    
    /* Listen for connection from predecessors */
    conn_data_t conn_data = {
        .rcount = data.outstanding,
        .scount = data.outstanding,
        .rbuf_len = data.max_buf_size / data.outstanding,
        .sbuf_len = 64,
        
        .on_connection = new_predecessor,
        .destroy_ep_data = ac_destroy_prev_srv,
        .handle_data = handle_prev_data,
    };
    memcpy(conn_data.ei.port, data.self_ni.ac_port, sizeof(conn_data.ei.port));
    data.prev_srv_ch = ac_net_mod->ilisten(&conn_data);
    if (NULL == data.prev_srv_ch) {
        error("ilisten\n");
        terminate(1);
    }

    /* Publish listening port */
    // TODO: use ZooKeeper for this !! 
    sprintf(filename, "p%"PRIu32".id", data.self);
    FILE *stream = fopen(filename, "w+");
    fprintf(stream, "%s %s\n", data.self_ni.host, conn_data.ei.port);
    fclose(stream);
    //memcpy(data.self_ni.ac_port, conn_data.ei.port, sizeof conn_data.ei.port);
    info_wtime("Published own ID (hostname and port) -- %s:%s\n", data.self_ni.host, conn_data.ei.port);
                
    /* Wait for the port number to be published */
    for (sid = 0; sid < data.n; sid++) {
        srv = &data.vertex_to_srv_map[sid];
        sprintf(filename, "p%"PRIu32".id", sid);
        while (1) {
            if (access(filename, F_OK) != -1) {
                break;
            }
        }
        stream = fopen(filename, "r");
        if (NULL == stream) {
            error("cannot open server file %s\n", filename);
            terminate(1);
        }
        word = NULL;
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
            memset(srv->srv_value->ni.ac_port, 0, sizeof srv->srv_value->ni.ac_port);
            word = strtok(line," \t\r\n");
            word = strtok(NULL," \t\r\n");
            strcpy(srv->srv_value->ni.ac_port, word);
        }
        fclose(stream);
        //info_wtime("p%"PRIu32"'s ID -- %s:%s\n", sid, srv->srv_value->ni.host, srv->srv_value->ni.ac_port);
    }
    info_wtime("Done reading published IDs\n");
    
    /* Start the FD thread; 
     * Note: this also sets up the datagram transfer */
    memset(&data.fd.ud, 0, sizeof data.fd.ud);
    pthread_mutex_init(&data.quit_mutex, NULL);
    pthread_mutex_init(&data.fd.next_mutex, NULL);
    pthread_cond_init(&data.fd.cond, NULL);
    pthread_mutex_init(&data.fd.prev_mutex, NULL);
    pthread_mutex_lock(&data.quit_mutex);
    rv = pthread_create(&data.fd_thread, NULL, failure_detector, NULL);
    if (rv) {
        error("pthread_create (%s)\n", strerror(errno));
        terminate(1);
    }
    fd_thread_created = 1;
    
    /* Wait for the setup of the datagram transfer */
    pthread_mutex_lock(&data.fd.next_mutex);
    while (!data.fd.ud.conn && !data.fd.error) {
        pthread_cond_wait(&data.fd.cond, &data.fd.next_mutex);
    }
    pthread_mutex_unlock(&data.fd.next_mutex);
    if (data.fd.error) {
        error("FD thread existed with error.\n");
        terminate(1);
    }
    
    /* Initiate connection to successors */
    digraph_t *G = data.G[data.activeG];
    for (i = 0; i < G->degree; i++) {
        sid = get_successor(G, data.self, i);
        if (UINT32_MAX == sid) {
            error("get_successor\n");
            terminate(1);
        }
        if (0 != connect_to(sid)) {
            error("cannot connect to server p%"PRIu32"\n", sid);
            terminate(1);
        }
    }

    /* Start the client listener */
    pthread_mutex_init(&data.clt_mutex, NULL);   
    rv = pthread_create(&data.c_listener, NULL, wait_for_clients, NULL);
    if (rv) {
        error("pthread_create (%s)\n", strerror(errno));
        terminate(1);
    }
    c_listener_created = 1;

#ifdef BENCHMARK    
    benchmark_init();
#endif 
}

/* ================================================================== */

static int 
join_allconcur(char *host, char *port)
{
    int rv;
    kvs_ht_reply_t reply;
    ep_t *ep, *prev = NULL;
    kvs_ht_cmd_t *join_cmd = NULL;
    uint32_t len;
    uint8_t *snapshot = NULL;
    ac_srv_t *ac_srv = NULL;
    
    /* New server trying to join */
    if (!strlen(host) || !strlen(port)) {
        error("Server or port unspecified\n");
        return 1;
    }

    ep = data.ac_srv_list;
    while (NULL != ep) {
        if ((strcmp(host, ep->cd.ei.host) == 0) && 
            (strcmp(port, ep->cd.ei.port) == 0))
        {
            break;
        }
        prev = ep;
        ep = ep->next;
    }
    if (ep == NULL) {
        /* New successor */
        ep = (ep_t*)malloc(sizeof(ep_t));
        if (!ep) {
            error("malloc (%s)\n", strerror(errno));
            return 1;
        }
        memset(ep, 0, sizeof(ep_t));
        ac_srv = (ac_srv_t*)malloc(sizeof(ac_srv_t));
        if (!ac_srv) {
            error("malloc (%s)\n", strerror(errno));
            return 1;
        }
        memset(ac_srv, 0, sizeof(ac_srv_t));
        ac_srv->state = READ_REPLY;
        ac_srv->buf = (uint8_t*)&ac_srv->reply;
        ep->data = ac_srv;

        ep->head = &data.ac_srv_list;
        ac_ep_add(ep);
    }
    if (ep->connected) {
        /* Already connected */
        return 0;
    }
    /* Set endpoint data */
    memcpy(ep->cd.ei.host, host, sizeof(ep->cd.ei.host));
    memcpy(ep->cd.ei.port, port, sizeof(ep->cd.ei.port));
    ep->cd.scount = 2;
    ep->cd.sbuf_len = data.max_buf_size / data.outstanding;
    ep->cd.rcount = 2;
    ep->cd.rbuf_len = data.max_buf_size / data.outstanding;
    ep->cd.on_connection = send_join_request;
    ep->cd.destroy_ep_data = ac_destroy_ac_srv;
    ep->cd.handle_data = handle_join_reply;

    /* Create connecting channel (if needed); use the same channel 
     * for connecting to successors */
    if ((NULL == data.next_srv_ch) && (ac_net_mod->create_ch)) {
        data.next_srv_ch = ac_net_mod->create_ch();
        if (!data.next_srv_ch) {
            error("create_ch\n");
            return 1;
        }
    }
    /* Connect */
    info_wtime("Connecting to %s:%s\n", host, port);
    rv = ac_net_mod->iconnect(ep, data.next_srv_ch);
    if (rv) {
        error("iconnect\n");
        return 1;
    }
    
    return 0;
}

static void* 
send_join_request(void *conn)
{
    int rv;
    uint32_t len, bytes;
    shared_buf_t *sh_buf = NULL;
    kvs_ht_cmd_t *join_cmd;
    conn_ctx_t *conn_ctx = (conn_ctx_t*)conn;
    ep_t *ep = conn_ctx->ep;

    info_wtime("Connected to %s:%s\n", ep->cd.ei.host, ep->cd.ei.port);
    ep->connected = 1;
                
    conn_ctx->buffering = 1;
        
    /* Create join CMD */
    len = sizeof(kvs_ht_cmd_t) + sizeof(net_id_t);
    bytes = sizeof(shared_buf_t) + len;
    sh_buf = (shared_buf_t*)malloc(bytes);
    if (NULL == sh_buf) {
        error("malloc (%s)\n", strerror(errno));
        return NULL;
    }
    memset(sh_buf, 0, bytes);
    sh_buf->len = bytes - sizeof(shared_buf_t);
    join_cmd = (kvs_ht_cmd_t*)sh_buf->buf;
    join_cmd->type = CTRL_JOIN;
    memcpy(join_cmd->data, &data.self_ni, sizeof(net_id_t));
    join_cmd->value_len = sizeof(net_id_t);

    /* Send join request (asynch) */
    info_wtime("Sending JOIN req (%"PRIu32" bytes)\n", len);
    rv = ac_net_mod->isend(ep, sh_buf);
    if (rv) {
        error("isend\n");
        return NULL;
    }
    if (!sh_buf->shared_count) {
        free(sh_buf);
        sh_buf = NULL;
    }

    return ep;
}

static void 
handle_join_reply(void *endpoint, void *recv_buf, uint32_t recv_len)
{
    int direct_cp, rv;
    uint32_t len, idx;
    static uint32_t n, rnines;
    kvs_ht_reply_t reply;
    void *snapshot;
    shared_buf_t *sh_buf;
    ep_t *ep = (ep_t*)endpoint;
    if (!ep) {
        error("endpoint is NULL\n");
        terminate(1);
    }
    ac_srv_t *ac_srv = (ac_srv_t*)ep->data;
    if (!ac_srv) {
        error("ac_srv is NULL\n");
        terminate(1);
    }
    if (!recv_buf) {
        error("recv_buf is NULL\n");
        terminate(1);
    }
    
    while (recv_len != 0) {
        direct_cp = 0;
        if (READ_REPLY == ac_srv->state) {
            /* Receiving a JOIN reply */
            len = sizeof(kvs_ht_reply_t) - ac_srv->byte_count;
            if (recv_len < len) {
                /* partially */
                memcpy(ac_srv->buf, recv_buf, recv_len);
                ac_srv->buf += recv_len;
                ac_srv->byte_count += recv_len;
                return;
            }
            /* complete */
            memcpy(ac_srv->buf, recv_buf, len);
            recv_buf += len;
            recv_len -= len;
        }
        else if (READ_SNAPSHOT == ac_srv->state) {
            goto copy_snapshot;
        }
        else {
            error("unknown state\n");
            terminate(1);
        }
    
        /* Received JOIN reply */
        if (RP_FULL == ac_srv->reply.type) {
            error("request pool is full\n");
            terminate(1);
        }
        if (0 != ac_srv->reply.rc) {
            info_wtime("Join request rejected\n");
            terminate(1);
        }
        /* Join request successful */
        consensus_sqn = ac_srv->reply.u.join.csqn;
        n = ac_srv->reply.u.join.n;
        rnines = ac_srv->reply.u.join.rnines;
        data.self = ac_srv->reply.u.join.sid;
        info_wtime("Join successful: sqn=%"PRIu64"; n=%"PRIu32"; r=%"PRIu32
            "; p%"PRIu32"\n", consensus_sqn, n, rnines, data.self);

        if (!ac_srv->reply.len && recv_len) {
            error("JOIN reply is inconsistent\n");
            terminate(1);
        }
        if (!recv_len) {
            goto join_completed;
        }

        ac_srv->state = READ_SNAPSHOT;
        if (ac_srv->reply.len == recv_len) {
            direct_cp = 1;
            goto got_snapshot;
        }
        /* Allocate space for SM snapshot */
        ac_srv->snapshot = (uint8_t*)malloc(ac_srv->reply.len);
        if (!ac_srv->snapshot) {
            error("malloc %s\n", strerror(errno));
            terminate(1);
        }
        ac_srv->buf = ac_srv->snapshot;
        ac_srv->byte_count = 0;

copy_snapshot:        
        len = ac_srv->reply.len - ac_srv->byte_count;
        if (recv_len < len) {
            /* partially */
            memcpy(ac_srv->buf, recv_buf, recv_len);
            ac_srv->buf += recv_len;
            ac_srv->byte_count += recv_len;
            return;
        }
        /* complete */
        memcpy(ac_srv->buf, recv_buf, len);
        recv_buf += len;
        recv_len -= len;

got_snapshot:
        if (direct_cp) {
            snapshot = recv_buf;
        }
        else {
            snapshot = ac_srv->snapshot;
        }
        /* Create CTRL SM */
        if (0 != ac_srv->reply.u.join.ctrl_len) {
            data.ctrl_sm = new_ctrl_sm();
            if (NULL == data.ctrl_sm) {
                error("new_ctrl_sm\n");
                terminate(1);
            }
            /* Apply snapshot */
            rv = apply_kvs_snapshot(data.ctrl_sm, snapshot, 
                            ac_srv->reply.u.join.ctrl_len);
            if (0 != rv) {
                error("apply_kvs_snapshot\n");
                terminate(1);
            }
#if 1
info_wtime("Created CTRL SM %"PRIu32" bytes\n", 
            ac_srv->reply.u.join.ctrl_len);
//print_kvs(data.ctrl_sm);
#endif
        }
#ifdef AC_KVS
        len = ac_srv->reply.len - ac_srv->reply.u.join.ctrl_len;
        if (len) {
            /* Create KVS */
            if (NULL == data.kvs) {
                error("create_kvs_ht\n");
                terminate(1);
            }
            /* Apply snapshot */
            rv = apply_kvs_snapshot(data.kvs, 
                snapshot+ac_srv->reply.u.join.ctrl_len, len);
            if (0 != rv) {
                error("apply_kvs_snapshot\n");
                terminate(1);
            }
//~ info_wtime("Created KVS %"PRIu32" bytes\n", len);
//~ print_kvs(data.kvs);
        }
#endif

join_completed:
        /* Free list of AllConcur servers */
        while (NULL != (ep = data.ac_srv_list)) {
            data.ac_srv_list = ep->next;
            ac_ep_destroy(ep);
        }
        /* Initialize AllConcur */
        init_allconcur(n, rnines);
        join = 0;
        info_wtime("Join operation was successful\n");
        break;
    }
}

/* ================================================================== */
       
static void
poll_cb(EV_P_ ev_idle *w, int revents)
{
    int rv, outstanding_sends;
    ep_t *ep;

    poll_count++;

#if 0
    static uint64_t count = 0;
    
    if (!count && !join) {
        count=1;
    }
    //count++;
    if (count == 1000) {
        count = 0;
    }
#endif    

    if (recv_sigint) {
        terminate(0);
    }

    /* Poll for outgoing connections (to servers) */
    if (ac_net_mod->poll_ch) {
        rv = ac_net_mod->poll_ch(data.next_srv_ch);
        if (rv) {
            error("poll_ch\n");
            terminate(1);
        }
    }

    if (join) {
        /* Poll for join request/reply completion */
        if (ac_net_mod->poll_send) {
            ep = data.ac_srv_list;
            while (NULL != ep) {
                if (!ep->connected)
                    goto next_server;
                outstanding_sends = ac_net_mod->poll_send(ep);
                if (-1 == outstanding_sends) {
                    error("poll_send\n");
                    terminate(1);
                }
                rv = ac_net_mod->poll_recv(ep);
                if (rv) {
                    error("poll_recv\n");
                    terminate(1);
                }
                if (!join) break;
next_server:
                ep = ep->next;
            }
        }
        return;
    }

    /* Poll for incoming connections (from servers) */
    if (ac_net_mod->poll_ch) {
        rv = ac_net_mod->poll_ch(data.prev_srv_ch);
        if (rv) {
            error("poll_ch\n");
            terminate(1);
        }
    }
    
    /* Poll for incomming data... */
    if (ac_net_mod->poll_recv) {
        /* ...from predecessors */
        ep = data.prev_srv_list;
        while (NULL != ep) {
            if (ep->connected) {
                rv = ac_net_mod->poll_recv(ep);
                if (rv) {
                    error("poll_recv\n");
                    terminate(1);
                }            
            }
            ep = ep->next;
        }
#ifdef AVOID_REDUNDANT
        /* ...from successors */
        ep = data.next_srv_list;
        while (NULL != ep) {
            if (ep->connected) {
                rv = ac_net_mod->poll_recv(ep);
                if (rv) {
                    error("poll_recv\n");
                    terminate(1);
                }        
            }    
            ep = ep->next;
        }
#endif        
    }
    
    /* Poll completion of send operations */
    if (ac_net_mod->poll_send) {
        /* ...towards successors */
        int done_sending = 1;
        ep = data.next_srv_list;
        while (NULL != ep) {
            if (ep->data) {
                next_srv_t *next_srv = (next_srv_t*)ep->data;
                if (server_is_failed(next_srv->sid)) 
                    goto next_successor;
                if (server_failed_crt_round(next_srv->sid))
                    goto next_successor;
            }
            if (!ep->connected)
                goto next_successor;
            outstanding_sends = ac_net_mod->poll_send(ep);
            if (-1 == outstanding_sends) {
                error("poll_send\n");
                terminate(1);
            }
            if (outstanding_sends > 0) 
                done_sending = 0;
next_successor:
            ep = ep->next;
        }
        if (!ac_net_mod->bytes_to_send) {
            /* No queued messages to send */
            if (done_sending) {
                /* No outstanding sends */
                if (ac_net_mod->on_send_completed) {
                    /* Send completed */
                    ac_net_mod->on_send_completed();   
                }
            }
        }

#ifdef AVOID_REDUNDANT
        /* ...towards predecessors */
        ep = data.prev_srv_list;
        while (NULL != ep) {
            if (ep->data) {
                prev_srv_t *prev_srv = (prev_srv_t*)ep->data;
                if (prev_srv->sid != UINT32_MAX &&
                    server_is_failed(prev_srv->sid))
                    goto next_predecessor;
                if (prev_srv->sid != UINT32_MAX &&
                    server_failed_crt_round(prev_srv->sid))
                    goto next_predecessor;
            }
            if (!ep->connected)
                goto next_predecessor;
            outstanding_sends = ac_net_mod->poll_send(ep);
            if (-1 == outstanding_sends) {
                error("poll_send\n");
                terminate(1);
            }            
next_predecessor:
            ep = ep->next;
        }
#endif
    }

    
    /* Poll failure notifications */
    poll_fd();
    
    /* Poll the request pool */
    poll_request_pool();
    
    /* Check whether the digraph needs to be updated 
       either enough not answer join requests 
       or too many failures (low reliability) */   
    // TODO
}

#endif
