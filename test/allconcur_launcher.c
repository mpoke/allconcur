/**                                                                                                      
 * AllConcur
 * 
 * MPI launcher for AllConcur
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <signal.h>
#include <errno.h>
#include <sys/wait.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <limits.h>
#include <libgen.h>
#include <getopt.h>
#include <sys/time.h>
#include <netdb.h>

#include <mpi.h>

#define RANGE "1024:1024"

#define BENCH_LATENCY       1
#define BENCH_TREQ          2
#define BENCH_CTREQ         3
#define BENCH_THROUGHPUT    5
#define BENCH_FAILURE       6

#define AC_NET_IBV 1
#define AC_NET_TCP 2

#define START_PORT 55000

//#define MEMCHECK

pid_t pid;
char hostname[HOST_NAME_MAX];
int cpurank, server_count;
int mpirank;
char *bin_path;


int bench_type = BENCH_THROUGHPUT;
#ifdef AC_IBV            
int net_type = AC_NET_IBV;
#else
int net_type = AC_NET_TCP;
#endif
int timer = 0;

static int
start_server(int p);
void fail_join(int rank, int fail_delay, int join_delay, int proxy)
{
    if (mpirank == rank) {
        /* Stop server */
        struct timeval tv;
        sleep(fail_delay);
        kill(pid, SIGINT);
        gettimeofday(&tv,NULL);
        printf("[%lu:%06lu] %s#%d fails\n", tv.tv_sec, tv.tv_usec, hostname, cpurank);
        
        /* Start server */
        sleep(join_delay);
        pid = start_server(proxy);
    }
}


static int
cmpfunc_int(const void *a, const void *b)
{
    return ( *(int*)a - *(int*)b );
}
static void 
int_handler(int signum, siginfo_t *info, void *ptr);

static void 
usage(char *prog)
{
    printf("Usage: %s [OPTIONS]\n"
            "OPTIONS:\n"
            "\t-n <size>                    number of nodes\n"
#ifdef AC_IBV            
            "\t[--tcp | --ibv]              server-interconnection type (default=ibv)\n"
#else
            "\t[--tcp]                      server-interconnection type (default=tcp)\n"
#endif            
            "\t[-r <k-nines>]               required reliability (default=6)\n"
            "\t[-p <port>]                  inter-server port (default=55000)\n"
            "\t[-s <size>]                  request size in bytes (default=64)\n"
            "\t[--timer]                    timer\n"
            "\t[--treq]                     run request rate benchmark\n"
            "\t[--ctreq]                    run constant request rate benchmark\n"
            "\t   [-P <req_period>]         [treq|ctreq] period of generating request in ms (default=1)\n"
            "\t[--latency]                  run latency benchmark\n"
            "\t[--throughput]               run peak throughput benchmark (default)\n"
            "\t   [-b <batching factor>]    [throughput] max batching factor (default=512)\n"
            "\t[--failure]                  run failure benchmark\n",
            prog);
}

char proto[8];
char reliab[8];

int main(int argc, char** argv) 
{
    char path[PATH_MAX];
    char filename[NAME_MAX];
    char datafile[NAME_MAX];
    char vlogfile[NAME_MAX];
    char line[LINE_MAX];
    char host[HOST_NAME_MAX];
    char *word;
    char *port_str;
    char *client = NULL;
    int rc, i, j;
    int port, start_port = START_PORT;
    int nprocs, cid;
    int client_count = 0, id, rnines = 6;
    int *ids = NULL, *cpuranks = NULL;
    char *hosts = NULL;
    FILE *srv_stream = NULL, *cfg_stream = NULL;
    struct sigaction act;
    double req_period = 1;
    int c;
    int req_size = 64, max_batching = 512;
    
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
            {"treq",   no_argument, &bench_type, BENCH_TREQ},
            {"ctreq",   no_argument, &bench_type, BENCH_CTREQ},
            {"latency", no_argument, &bench_type, BENCH_LATENCY},
            {"throughput",  no_argument, &bench_type, BENCH_THROUGHPUT},
            {"failure",   no_argument, &bench_type, BENCH_FAILURE},
            {0, 0, 0, 0}
        };
        int option_index = 0;
        c = getopt_long (argc, argv, "hn:r:P:p:s:b:",
                       long_options, &option_index);
        /* Detect the end of the options. */
        if (c == -1) break;

        switch (c) {
            case 0:
                /* If this option set a flag, do nothing else now. */
                if (long_options[option_index].flag != 0)
                    break;
                printf("option %s", long_options[option_index].name);
                if (optarg)
                    printf(" with arg %s", optarg);
                printf("\n");
                break;

            case 'h':
                usage(argv[0]);
                exit(1);
                
            case 'n':
				server_count = atoi(optarg);
                break;
            
            case 'r':
                rnines = atoi(optarg);
                break;

            case 's':
                req_size = atoi(optarg);
                break;
            
            case 'b':
                max_batching = atoi(optarg);
                break;

            case 'p':
                start_port = atoi(optarg);
                break;
            
            case 'P':
                req_period = (double)atof(optarg);
                break;
    
            case '?':
                break;

            default:
                exit(1);
        }
    }
    
    if (req_size < 40) {
        printf("ERROR: the request cannot be less than 40 bytes\n");
        exit(1);
    }   
    if (!server_count) {
        printf("ERROR: server count not specified\n");
        usage(argv[0]);
        exit(1);
    }
    switch (net_type) {
        case AC_NET_IBV:
            sprintf(proto, "--ibv");
            break;
        default:
            sprintf(proto, "--tcp");
    }
    sprintf(reliab, "%d", rnines);
    
    double timeout, hb, warmup;
    if (BENCH_FAILURE == bench_type) {
        timeout = 0.1;
    }
    else {
        timeout = 1;
    }
    hb = 0.01;
    warmup = 10;
    
    char *binary;
    binary = strdup(argv[0]);
    bin_path = dirname(binary);
    free(binary);

    /* Set handler for SIGINT */
    memset(&act, 0, sizeof(act));
    act.sa_flags = SA_SIGINFO;
    act.sa_sigaction = int_handler;
    sigaction(SIGINT, &act, NULL);

    
    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
    MPI_Comm_rank(MPI_COMM_WORLD, &mpirank);

    if (server_count > nprocs) {
        printf("Error: not enough processes -- server_count=%d\n", server_count); 
        MPI_Finalize();
        exit(1);
    }
    
    gethostname(hostname, HOST_NAME_MAX);
    //printf("#%d: %s\n", mpirank, hostname);
    if (((hostname[0] == 'n') && (hostname[1] != 'i')) ||   // HLRS, not xc40
                (hostname[0] == 'i'))   // SuperMUC
    {
        sprintf(hostname, "%s-ib", hostname);
    }

    /* Check whether all servers see the allconcur binary */
    char is_binary = 1, is_binaries = 0;
    if (mpirank < server_count) {
        sprintf(path, "%s/allconcur", bin_path);
        if(access(path, F_OK) == -1) {
            /* Binary does not exist */
            printf("Error: [%s] cannot find binary %s\n", hostname, path);
            is_binary = 0;
        }
    }
    MPI_Allreduce(&is_binary, &is_binaries, 1, MPI_CHAR, MPI_LAND, MPI_COMM_WORLD);
    if (!is_binaries) {
        MPI_Finalize();
        return 1;
    }

#if 0    
    ids = (int*)malloc(nprocs*sizeof(int));
    if (NULL == ids) {
        printf("Error: allocating ids\n");
        exit(1);
    }
    memset(ids, 0, nprocs*sizeof(int));
    MPI_Allgather(&id, 1, MPI_INT, ids, 1, MPI_INT, MPI_COMM_WORLD);

    /* Compute rank on CPU */
    for (i = 0; i < mpirank; i++) {
        if (id == ids[i]) cpurank++;
    }
#else     
    hosts = (char*)malloc(nprocs*HOST_NAME_MAX);
    if (NULL == hosts) {
        printf("Error: allocating hosts\n");
    }
    memset(hosts, 0, nprocs*HOST_NAME_MAX);
    MPI_Allgather(hostname, HOST_NAME_MAX, MPI_CHAR, hosts, HOST_NAME_MAX, MPI_CHAR, MPI_COMM_WORLD);

    /* Compute rank on CPU */
    for (i = 0; i < mpirank; i++) {
        if (strncmp(hostname, hosts + i*HOST_NAME_MAX, HOST_NAME_MAX) == 0) cpurank++;
    }
#endif    

    cpuranks = (int*)malloc(nprocs*sizeof(int));
    if (NULL == cpuranks) {
        printf("Error: allocating cpuranks\n");
        exit(1);
    }
    memset(cpuranks, 0, nprocs*sizeof(int));
    MPI_Gather(&cpurank, 1, MPI_INT, cpuranks, 1, MPI_INT, 0, MPI_COMM_WORLD);

    /* Create allconcur.servers file */
//  qsort(ids, nprocs, sizeof(int), cmpfunc_int);
    if (0 == mpirank) {
        srv_stream = fopen("allconcur.servers", "w+");
        if (NULL == srv_stream) {
            printf("cannot open server file\n");
            exit(1);
        }
        for (i = 0; i < server_count; i++) {
            port = start_port + cpuranks[i]*3;
#if 0            
            fprintf(srv_stream, "n%06d-ib %d %d %d\n", 
                            ids[i], port, port+1, port+2);
#else 
            fprintf(srv_stream, "%s %d %d %d\n", 
                            hosts + i*HOST_NAME_MAX, port, port+1, port+2);
#endif             
        }
        fclose(srv_stream);
    }

    free(hosts);
    free(cpuranks);
    
    /* Wait for allconcur.server */
    MPI_Barrier(MPI_COMM_WORLD);
    

    pid = fork();
    if (0 == pid) {                                  /* Child process */
        if (mpirank < server_count) {
            /* Server: create config file */
            sprintf(filename, "srv_%s#%d.cfg", hostname, cpurank);
            cfg_stream = fopen(filename, "w+");
            if (NULL == cfg_stream) {
               printf("cannot open config file\n");
               exit(1);
            }
 
            /* AllConcur logging */
            sprintf(filename, "srv_%s#%d.log", hostname, cpurank);
            fprintf(cfg_stream, "log_file %s\n", filename);

            /* FD logging */
            sprintf(filename, "srv_%s#%d.fd", hostname, cpurank);
            fprintf(cfg_stream, "fd_file %s\n", filename);
            
            sprintf(filename, "srv_%s#%d.delay", hostname, cpurank);
            fprintf(cfg_stream, "delay-file %s\n", filename);

            /* t-round-file (for AllConcur) */
            sprintf(filename, "srv_%s#%d.tround", hostname, cpurank);
            fprintf(cfg_stream, "t-round-file %s\n", filename);
            
            /* t-request-file (for AllConcur) */
            sprintf(filename, "srv_%s#%d.trequest", hostname, cpurank);
            fprintf(cfg_stream, "t-request-file %s\n", filename);
            
            /* throughput-file (for AllConcur) */
            sprintf(filename, "srv_%s#%d.throughput", hostname, cpurank);
            fprintf(cfg_stream, "throughput-file %s\n", filename);
            
            /* request size */
            fprintf(cfg_stream, "req_size %d\n", req_size);

            /* max batching factor */
            fprintf(cfg_stream, "max_batching %d\n", max_batching);
            
            if (BENCH_CTREQ == bench_type) {
                /* Constant request generating rate per system */
                fprintf(cfg_stream, "req_period %9.7lf %9.8lf\n", 
                        req_period*server_count, 
                        0.1*req_period*server_count);
            }
            else {
                /* Constant request generating rate per server */
                fprintf(cfg_stream, "req_period %9.7lf %9.8lf\n", 
                            req_period, 0.1*req_period);
            }

            port = start_port + cpurank*3;
            fprintf(cfg_stream, "self %s %d %d %d\n", 
                    hostname, port, port+1, port+2);

            /* file with servers */
            fprintf(cfg_stream, "server_file allconcur.servers\n");

            /* timeout (in seconds) */
            fprintf(cfg_stream, "timeout %lf\n", timeout);

            /* heartbeat period (in seconds) */
            fprintf(cfg_stream, "hb_period %lf\n", hb);

            /* warm-up period (in seconds) */
            fprintf(cfg_stream, "warmup_period %lf\n", warmup);
            fclose(cfg_stream);
            
            sprintf(path, "%s/allconcur", bin_path);
            
            char sc[8];
            sprintf(sc, "%d", server_count);
            sprintf(filename, "srv_%s#%d.cfg", hostname, cpurank);
            
#ifndef MEMCHECK
            if (BENCH_LATENCY == bench_type) {
                rc = execl(path, "allconcur", "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--latency", proto,
                    (char *)0);
            }
            else if (BENCH_THROUGHPUT == bench_type) {
                rc = execl(path, "allconcur", "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--throughput", proto,
                    (char *)0);
            }
            else if (BENCH_FAILURE == bench_type) {
                rc = execl(path, "allconcur", "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--failure", proto,
                    (char *)0);
            }
            else {
                rc = execl(path, "allconcur", "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", proto,
                    (char *)0);
            }
            if (-1 == rc) {
                printf("[p%d] Error: execl %d (%s)\n", mpirank, errno, strerror(errno));
            }
#else
            sprintf(vlogfile, "--log-file=srv_%s#%d.mem", hostname, cpurank);
            //system("module load valgrind");
            FILE *fp = popen("which valgrind", "r");
            if (!fp) {
                printf("Failed to run command \"which valgrind\"\n");
                exit(1);
            }
            char valgrind_path[128];
            if (NULL == fgets(valgrind_path, sizeof(valgrind_path), fp)) {
                printf("No Valgrind\n");
                exit(1);
            }
            /* Remove trailing newline */
            valgrind_path[strcspn(valgrind_path, "\r\n")] = 0;

            if (BENCH_LATENCY == bench_type) {
                rc = execl(valgrind_path, "valgrind",
                    vlogfile, "--leak-check=full", "--track-origins=yes",
                        path, "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--latency", proto,
                    (char *)0);
            }
            else if (BENCH_THROUGHPUT == bench_type) {
                rc = execl(valgrind_path, "valgrind",
                    vlogfile, "--leak-check=full", "--track-origins=yes",
                        path, "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--throughput", proto,
                    (char *)0);
            }
            else if (BENCH_FAILURE == bench_type) {
                rc = execl(valgrind_path, "valgrind",
                    vlogfile, "--leak-check=full", "--track-origins=yes",
                        path, "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", "--failure", proto,
                    (char *)0);
            }
            else {
                rc = execl(valgrind_path, "valgrind",
                    vlogfile, "--leak-check=full", "--track-origins=yes",
                        path, "-n", sc, "-r", reliab, 
                    "-c", filename, "--timer", proto,
                    (char *)0);
            }
            if (-1 == rc) {
                printf("[p%d] Error: execl (%s)\n", mpirank, strerror(errno));
            }

#endif
        }
        else if (NULL != client) {
            /* possible client */
            cid = mpirank - server_count;
            if (cid >= client_count) return 0;

            sprintf(filename, "clt%06d.log", cid);
            sprintf(datafile, "clt%06d.data", cid);
            
            /* I'm a client */
            cid = cid % server_count;   // connect to this server
            srv_stream = fopen("allconcur.servers", "r");
            if (NULL == srv_stream) {
               printf("cannot open server file\n");
               exit(1);
            }
            i = -1;
            while (fgets(line, LINE_MAX, srv_stream)) { 
                /* Remove trailing newline */
                line[strcspn(line, "\r\n")] = 0;
                /* Parse each line */
                if (line[0] == '#') continue;
                if (line[0] == '\n') continue;
                i++;
                
                /* hostname */
                word = strtok(line," \t\r\n");
                if (strcmp(word, hostname) == 0) {
                    /* Same hostname as me -- let's connect here */
                    strcpy(host, word);
                    /* FD port */
                    strtok(NULL," \t\r\n");
                    /* inter-server port */
                    strtok(NULL," \t\r\n");
                    /* client port */
                    port_str = strtok(NULL," \t\r\n");
                    break;
                }
                else if (i == cid) {
                    /* This could be a solution if there is nobody locally */
                    strcpy(host, word);
                    /* FD port */
                    strtok(NULL," \t\r\n");
                    /* inter-server port */
                    strtok(NULL," \t\r\n");
                    /* client port */
                    port_str = strtok(NULL," \t\r\n");
                    continue;
                }
            }
            fclose(srv_stream);

            //printf("CLIENT: connecting to p%06d [%s:%s] (log file=%s; data file=%s)\n", cid, host, port_str, filename, datafile);

            sprintf(path, "%s/%s", bin_path, client);
            rc = execl(path, client,
                    "-s", host, "-p", port_str, "-l", filename,
                    "-d", datafile, "-r", RANGE, "--timer",
                    (char *)0);
            if (-1 == rc) {
                printf("Error: execl (%s)\n", strerror(errno));
            }
        }
        
        return 0;
    }

    if (BENCH_FAILURE == bench_type) {
        if (server_count < 32) {
            goto terminate_fail_scenario;
        }
        
        const int fj_time = 5;
        const int ff_time = 3;
        const int round_time = 10;
        struct timeval tv;
        if (mpirank == 0) {
            gettimeofday(&tv,NULL);
            printf("[%lu:%06lu] Start failure benchmark\n", tv.tv_sec, tv.tv_usec);
        }
        sleep(60);
        
        MPI_Barrier(MPI_COMM_WORLD);

        /* Fail mpirank 2 after 0 sec and then join via mpirank 0 */
        fail_join(2, 0, fj_time, 0);
        MPI_Barrier(MPI_COMM_WORLD);
        sleep(round_time);
    
#if 1
        /* Fail mpirank 11 after 0 sec and then join via mpirank 0 */
        fail_join(11, 0, fj_time, 0);
        MPI_Barrier(MPI_COMM_WORLD);
        sleep(round_time);
#endif    

#if 1   
        /* Fail mpirank 4 and then join via mpirank 10 */
        fail_join(4, 0, ff_time+fj_time, 10);
        /* Fail mpirank 1 and then join via mpirank 3 */
        fail_join(1, ff_time, ff_time + fj_time, 3);
        MPI_Barrier(MPI_COMM_WORLD);
        sleep(round_time);
#endif    


#if 1
        /* Fail mpirank 5 after 0 sec and then join via mpirank 12 */
        fail_join(5, 0, 2*ff_time+fj_time, 12);
        /* Fail mpirank 13 and then join via mpirank 0 */
        fail_join(13, ff_time, 2*ff_time + fj_time, 0);
        /* Fail mpirank 21 and then join via mpirank 22 */
        fail_join(21, 2*ff_time, 2*ff_time + fj_time, 22);
        MPI_Barrier(MPI_COMM_WORLD);
        sleep(round_time);
#endif    
    
terminate_fail_scenario:    
        kill(pid, SIGINT);
        int status;
        waitpid(pid, &status, 0);
        MPI_Barrier(MPI_COMM_WORLD);
        MPI_Finalize();
        return 0;
    }

#if 0
    sleep(20);
        kill(pid, SIGINT);
    MPI_Finalize();
    return 0;
#endif

    /* Wait for the server to finish */
    int status;
    waitpid(pid, &status, 0);
    if (WIFEXITED(status)) {
        printf("%s#%d terminated normally (rc=%d)\n", 
            hostname, cpurank, WEXITSTATUS(status));
    }
    else if (WIFSIGNALED(status)) {
        printf("%s#%d terminated by signal %d (core_dump=%s)\n", 
            hostname, cpurank, WTERMSIG(status), (WCOREDUMP(status) ? "yes" : "no"));
    }
    
    MPI_Finalize();
    return 0;
}

static void 
int_handler(int signum, siginfo_t *info, void *ptr)
{
    printf("[%s:%s:%d] Received signal %d\n", 
           __FILE__, __func__, __LINE__, signum);
    printf("Signal originates from process %lu\n",
            (unsigned long)info->si_pid);
    kill(pid, SIGINT);
    exit(1);
}

static int
start_server(int p)
{
    int rc, i;
    FILE* srv_stream = NULL;
    char line[LINE_MAX];
    char filename[NAME_MAX];
    char vlogfile[NAME_MAX];
    char path[PATH_MAX];
    char host[NI_MAXHOST];
    char port[NI_MAXSERV];
    char *word;

    pid = fork();
    if (0 == pid) {
        srv_stream = fopen("allconcur.servers", "r");
        if (NULL == srv_stream) {
            printf("cannot open server file\n");
            exit(1);
        }
        i = -1;
        while (fgets(line, LINE_MAX, srv_stream)) { 
            /* Remove trailing newline */
            line[strcspn(line, "\r\n")] = 0;
            /* Parse each line */
            if (line[0] == '#') continue;
            if (line[0] == '\n') continue;
            i++;
            if (i == p) {
                word = strtok(line," \t\r\n");
                memset(host, 0 , NI_MAXHOST);
                sprintf(host, "%s", word);
                word = strtok(NULL," \t\r\n");
                memset(port, 0 , NI_MAXSERV);
                sprintf(port, "%s", word);
                break;
            }
        }
        fclose(srv_stream);
        printf("try to connect via %s:%s\n", host, port);
        
        /* Read client listening port from published file */
        sprintf(filename, "srv_%s#%s.clt", host, port);
        while (1) {
            if (access(filename, F_OK) != -1) {
                break;
            }
        }
        srv_stream = fopen(filename, "r");
        if (NULL == srv_stream) {
            printf("cannot open file %s\n", filename);
            exit(1);
        }
        word = NULL;
        while (fgets(line, LINE_MAX, srv_stream)) { 
            /* Parse each line */
            if (line[0] == '#') continue;
            if (line[0] == '\n') continue;
            /* Remove trailing newline */
            line[strcspn(line, "\r\n")] = 0;
            if (strcmp(line, "") == 0) {
                if (!word) {
                    fseek(srv_stream, 0, SEEK_SET);
                    continue;
                }
                else 
                    break;
            }
            word = strtok(line," \t\r\n");
        }
        memset(port, 0 , NI_MAXSERV);
        sprintf(port, "%s", word);
        fclose(srv_stream);
        
        char sc[8];
        sprintf(sc, "%d", server_count);
        sprintf(filename, "srv_%s#%d.cfg", hostname, cpurank);
        
        struct timeval tv;
        gettimeofday(&tv,NULL);
        printf("[%lu:%06lu] %s#%d joins (via %s)\n", tv.tv_sec, tv.tv_usec, hostname, cpurank, host, port);
        sprintf(path, "%s/allconcur", bin_path);
#if 1        
        rc = execl(path, "allconcur", "-n", sc, "-r", reliab, 
                    "-c", filename, "--join", "-s", host, "-p", word, "--failure",
                    proto, (char *)0);
#else
        sprintf(vlogfile, "--log-file=srv_%s#%d.mem", hostname, cpurank);
        rc = execl("/usr/bin/valgrind", "valgrind",
                    vlogfile, "--leak-check=full", "--track-origins=yes",
                    path, "-n", sc, "-r", reliab, 
                    "-c", filename, "--join", "-s", word, "-p", port_str, "--failure",
                    proto, (char *)0);

#endif        
        if (-1 == rc) {
            printf("Error: execl (%s)\n", strerror(errno));
        }
    }
    return pid;
}
