/**                                                                                                      
 * AllConcur
 * 
 * Endpoint
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef AC_EP_H
#define AC_EP_H

#include <ac_net.h>
#include <ac_timer.h>

/* ================================================================== */
/* data structures needed by ep->data */

struct message_t {
#ifdef MSG_DELAY
    HRT_TIMESTAMP_T t;
#endif    
    uint64_t sqn;                           /* consensus sequence number */
    uint32_t owner;                               /* the original sender */
    uint32_t inlen_fail;                   /* INPUT len or failed server */
    uint8_t type;
    uint8_t padding[7];
    uint8_t input[0];
};
typedef struct message_t message_t;

struct message_queue_t {
    struct message_queue_t *next;
    uint32_t completed;
    uint32_t from_sid;
    message_t msg;
};
typedef struct message_queue_t message_queue_t;

struct cid_t {
    uint64_t srv_sqn;
    uint64_t clt_sqn;
};
typedef struct cid_t cid_t;

/* KVS command -- send by clients */
struct kvs_ht_cmd_t {
    cid_t       cid;
    uint64_t       sqn; 
    uint16_t    key_len;    /* including '\0' */
    uint16_t    value_len;
    uint8_t     type;   // KVS_PUT, KVS_GET, KVS_RM
    uint8_t     padding[3];
    uint8_t     data[0];
};
typedef struct kvs_ht_cmd_t kvs_ht_cmd_t;

/* KVS reply -- answer to a command */
struct kvs_ht_reply_t {
    union {
        struct {
            cid_t       cid;
            uint64_t       sqn;
        } sm;
        struct {
            uint64_t       csqn;
            uint32_t       sid;
            uint32_t    n;
            uint32_t    rnines;
            uint32_t    ctrl_len;
        } join;
    } u;
    uint32_t    len;
    uint8_t     type;   /* RC, WIP, FULL */
    uint8_t     rc;
    uint8_t     padding[2];
    uint8_t data[0];
};
typedef struct kvs_ht_reply_t kvs_ht_reply_t;


/* ================================================================== */
/* ep->data */

/* Successor */
struct next_srv_t {
    uint32_t sid;
    message_queue_t *messages;            /* list of pending messages */
    uint64_t round_sqn;
    uint64_t sqn;
    uint8_t *buf;
    uint32_t byte_count;
};
typedef struct next_srv_t next_srv_t;

/* Predecessor */
struct prev_srv_t {
    uint32_t sid;
    struct {
        uint32_t len;
        void *endpoint;
    } ud_info;
    message_t msg;
    uint64_t round_sqn;
#ifdef MSG_DELAY    
    HRT_TIMESTAMP_T t_send, t_recv;
#endif    
    uint8_t *buf;
    uint8_t *input;
    message_queue_t *q;
    uint32_t byte_count;
    uint32_t inlen;
    char state;
};
typedef struct prev_srv_t prev_srv_t;

/* AllConcur server -- used for joining */
struct ac_srv_t {
    kvs_ht_reply_t reply;
    uint8_t *snapshot;
    uint8_t *buf;
    uint32_t byte_count;
    uint8_t state;
};
typedef struct ac_srv_t ac_srv_t;

/* Client */
struct client_t {
    struct kvs_ht_cmd_t cmd;
    uint8_t *buf;
    uint8_t *data;
    uint32_t in;
    uint32_t byte_count;
    uint32_t data_len;
    uint8_t state;
    uint8_t wip;
};
typedef struct client_t client_t;

/* ================================================================== */
/* functions */
void ac_destroy_next_srv(void *next);
void ac_destroy_prev_srv(void *prev);
void ac_destroy_ac_srv(void *server);
void ac_destroy_client(void *clt);


#endif /* AC_EP_H */
