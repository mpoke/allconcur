/**                                                                                                      
 * AllConcur 
 * 
 * Data types
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef AC_TYPES_H
#define AC_TYPES_H

#include <sys/socket.h>
#include <netdb.h>

#define SH_BUF_POSTED   1

struct sid_queue_t {
    struct sid_queue_t *next;
    uint32_t sid;
};
typedef struct sid_queue_t sid_queue_t;

struct tuple_t {
    uint32_t pp, ps;
};
typedef struct tuple_t tuple_t;

struct net_id_t {
    char host[NI_MAXHOST];
    char fd_port[NI_MAXSERV];
    char ac_port[NI_MAXSERV];
};
typedef struct net_id_t net_id_t;

struct srv_value_t {
    net_id_t ni;                         /* identifier in the network */
    uint64_t clt_sqn;                                   /* client SQN */
    //uint32_t sid;                        /* identifier inside graph */
    uint8_t failed;                                    /* failed flag */
};
typedef struct srv_value_t srv_value_t;

struct srv_t {
    uint64_t sqn;
    sid_queue_t *fn;                 /* List of failure notifications */
    void *input;                                    /* Server's input */
    srv_value_t *srv_value;        /* Sever's value in the control SM */
    uint32_t inlen;                                   /* Input length */
    uint32_t state;                                   /* Server state */
    uint8_t sent_data;
    uint8_t received_data;
};
typedef struct srv_t srv_t;

#endif /* AC_TYPES_H */
