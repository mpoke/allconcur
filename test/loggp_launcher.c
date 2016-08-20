/**                                                                                                      
 * AllConcur
 * 
 * MPI launcher for LogGP
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

#include <mpi.h>


#define AC_NET_IBV 1
#define AC_NET_TCP 2
#define AC_NET_RDMA 3

#define SRV_PORT "49913"

//#define MEMCHECK

pid_t pid;

#ifdef AC_IBV            
int net_type = AC_NET_IBV;
#else
int net_type = AC_NET_TCP;
#endif

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
#ifdef AC_IBV            
            "\t[--tcp | --ibv | --rdma]   server-interconnection type (default ibv)\n"
#else
            "\t[--tcp]                    server-interconnection type (default tcp)\n"
#endif            
            "\t-p <port>                  port\n",
            prog);
}

int main(int argc, char** argv) 
{
    char proto[8];
    char path[PATH_MAX];
    char lcl_host[HOST_NAME_MAX];
    char rmt_host[HOST_NAME_MAX];
    char vlogfile[NAME_MAX];
    char *srv_port = NULL;
    char *exe_path = NULL;
    int rc, i, j;
    int mpirank, nprocs;
    struct sigaction act;
    int c;

    /* Parse command line */
    while (1) {
        static struct option long_options[] = {
            /* These options set the type of the SM */
#ifdef AC_IBV            
            {"rdma", no_argument, &net_type, AC_NET_RDMA},
            {"ibv",  no_argument, &net_type, AC_NET_IBV},
#endif            
            {"tcp",   no_argument, &net_type, AC_NET_TCP},
            {0, 0, 0, 0}
        };
        int option_index = 0;
        c = getopt_long (argc, argv, "hp:",
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
            
            case 'p':
                srv_port = optarg;
                break;
    
            case '?':
                break;

            default:
                exit(1);
        }
    }
    
    switch (net_type) {
        case AC_NET_IBV:
            sprintf(proto, "--ibv");
            break;
        case AC_NET_RDMA:
            sprintf(proto, "--rdma");
            break;
        default:
            sprintf(proto, "--tcp");
    }

    if (!srv_port) {
        printf("Error: no port provided\n");
        usage(argv[0]);
        exit(1);
    }


    /* Set handler for SIGINT */
    memset(&act, 0, sizeof(act));
    act.sa_flags = SA_SIGINFO;
    act.sa_sigaction = int_handler;
    sigaction(SIGINT, &act, NULL);


    MPI_Init(&argc, &argv);
    MPI_Comm_size(MPI_COMM_WORLD, &nprocs);
    MPI_Comm_rank(MPI_COMM_WORLD, &mpirank);
    
    if (nprocs < 2) {
        printf("Not enough processes...\n");
        exit(1);
    }
    
    gethostname(lcl_host, HOST_NAME_MAX);

    /* Get absolute path of binaries */
    memset(path, 0, PATH_MAX);
    if (strncmp(lcl_host, "nid", 3) == 0) {
        /* Cannot use readlink to get the current path */
        sprintf(path, "/zhome/academic/HLRS/hlrs/hpcmapok/workspace/simtech/allconcur/bin/loggp_launcher");
    }
    else {
        pid = getpid();
        sprintf(path, "/proc/%d/exe", pid);
        if (readlink(path, path, PATH_MAX) == -1) {
            printf("Error: readlink (%s)", strerror(errno));
            exit(1);
        }
    }
    exe_path = dirname(strdup(path));


    if (0 == mpirank) {
        MPI_Send(lcl_host, HOST_NAME_MAX, MPI_CHAR, 1, 0, MPI_COMM_WORLD);
    }
    else if (1 == mpirank) {
        MPI_Status status;
        MPI_Recv(rmt_host, HOST_NAME_MAX, MPI_CHAR, 0, 0, MPI_COMM_WORLD, &status);
        if (strcmp(lcl_host,rmt_host) == 0) {
            printf("Same host...\n");
            exit(1);
        }
        if (((rmt_host[0] == 'n') && (rmt_host[1] != 'i')) ||
                (rmt_host[0] == 'i'))
        {
            /* LAKI - use IB network */
            sprintf(rmt_host, "%s-ib", rmt_host);
        }
        printf("Client on host %s; server on host %s\n", lcl_host, rmt_host);
    }
    
    pid = fork();
    if (0 == pid) {                                  /* Child process */
        sprintf(path, "%s/loggp", exe_path);
        if (0 == mpirank) {
            /* Server */
#ifndef MEMCHECK            
            rc = execl(path, "loggp", 
                    "-p", srv_port ? srv_port : SRV_PORT, "-l", "loggp_srv.log", proto,
                    (char *)0);
#else
            sprintf(vlogfile, "--log-file=loggp_srv.mem");        
            rc = execl("/usr/bin/valgrind", "valgrind",
                vlogfile, "--leak-check=full", "--track-origins=yes",
                path, "-p", srv_port ? srv_port : SRV_PORT, "-l", "loggp_srv.log", proto,
                (char *)0);
#endif                    
            if (-1 == rc) {
                printf("Error: execl (%s) (path=%s)\n", strerror(errno), path);
            }
        }
        else if (1 == mpirank) {
            /* Client */
            sleep(2);
#ifndef MEMCHECK              
            rc = execl(path, "loggp", 
                    "-s", rmt_host, "-p", srv_port ? srv_port : SRV_PORT, 
                    "-l", "loggp_clt.log",
                    "-o", "loggp.out", "--client", proto, 
                    (char *)0);
#else
            sprintf(vlogfile, "--log-file=loggp_clt.mem");
            rc = execl("/usr/bin/valgrind", "valgrind",
                vlogfile, "--leak-check=full", "--track-origins=yes",       
                path, "-s", rmt_host, "-p", srv_port ? srv_port : SRV_PORT, 
                "-l", "loggp_clt.log",
                "-o", "loggp.out", "--client", proto, 
                (char *)0);
#endif                    
            if (-1 == rc) {
                printf("Error: execl (%s) (path=%s)\n", strerror(errno), path);
            }
        }
        return 0;
    }

    /* Wait for the clients to finish */
    if (1 == mpirank) {
        int status;
        waitpid(pid, &status, 0);
    }
    MPI_Barrier(MPI_COMM_WORLD);
    if (0 == mpirank) {
        kill(pid, SIGINT);
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


