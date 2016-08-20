/**                                                                                                      
 * AllConcur
 * 
 * Failure detector
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
 
#ifndef AC_FD_H
#define AC_FD_H

#include <pthread.h>
#include <ev.h>

#define FD_EP_NEW		0
#define FD_EP_OLD 		1
#define FD_EP_ACTIVE 	2
#define FD_EP_FAILED 	3

//#define FD_DEBUG
#ifdef FD_DEBUG
#define FD_INFO
#endif
#define FD_INFO

struct fd_ep_t {
    struct fd_ep_t *next, *prev;
    void *endpoint;
    ev_tstamp hb_tstamp;
    uint64_t hb;
    uint64_t total_hb;
    uint64_t rounds;
    int checked;
    int state;
    uint32_t sid;
    uint64_t sqn;
};
typedef struct fd_ep_t fd_ep_t;

void *failure_detector();
void handle_fd_data(void *endpoint, void *recv_buf, uint32_t recv_len);

fd_ep_t* fd_add_endpoint(fd_ep_t **head, void *endpoint);
void fd_rm_ep(fd_ep_t **head, fd_ep_t *fd_ep);
void fd_print_endpoints(fd_ep_t *head);

void fd_stop();
void fd_start();

#endif /* AC_FD_H */
