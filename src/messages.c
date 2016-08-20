/**                                                                                                      
 * AllConcur
 * 
 * Message queue (for pending and premature messages)
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#include <stdlib.h>
 
#include <debug.h>
#include <allconcur.h>
#include <ac_algorithm.h>
#include <messages.h>
 
/* ================================================================== */
/* Type definitions */
#if 1

#endif 

/* ================================================================== */
/* Global variables */
#if 1

/* List of prematurely received messages */
message_queue_t *premature_msgs = NULL;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1


#endif

/* ================================================================== */
/* Global functions */
#if 1

/**
 * Adding a message to the list 
 * -> it also allocates space for the possible input 
 */
message_queue_t* add_message(message_queue_t **mq_ptr, 
                             message_t *msg, 
                             uint32_t from_sid)
{
    message_queue_t *q = NULL;
    uint32_t numbytes = sizeof(message_queue_t);
    
    if (MSG_INPUT == msg->type) {
        numbytes += msg->inlen_fail;
    }
//~ info("add_message: allocate %"PRIu32" type=%"PRIu8"; inlen=%"PRIu32"\n", numbytes, msg->type, msg->inlen_fail);
    
    if (NULL == *mq_ptr) {
        /* Empty list */
        q = (message_queue_t*)malloc(numbytes);
        if (NULL == q) {
            error("cannot allocate premature message\n");
            return NULL;
        }
        memset(q, 0, numbytes);
        q->from_sid = from_sid;
        memcpy(&q->msg, msg, sizeof(message_t));
        *mq_ptr = q;
        return q;
    }
    
    /* Find the end of the list */
    q = (message_queue_t*)(*mq_ptr);
    while (NULL != q->next) {
        q = q->next;
    }
    q->next = (message_queue_t*)malloc(numbytes);
    if (NULL == q->next) {
        error("cannot allocate premature message\n");
        return NULL;
    }
    memset(q->next, 0, numbytes);
    q->next->from_sid = from_sid;
    memcpy(&q->next->msg, msg, sizeof(message_t));
    return q->next;
}

/**
 * Destroy queue of messages
 */
void destroy_message_queue(message_queue_t **mq_ptr)
{
    message_queue_t *q;
    while ((q = *mq_ptr) != NULL) {
        *mq_ptr = q->next;
        free(q);    
    }
    *mq_ptr = NULL;
}

/** 
 * Send all pending messages (in order) 
 */
int send_pending_messages(ep_t *ep)
{
    int rv, flags, numbytes;
    message_queue_t *q;
    shared_buf_t *sh_buf = NULL;
    uint32_t len = 0;
    uint8_t *buf;
    
    if (!ep) {
        error("ep is NULL\n");
        return 1;
    }
    next_srv_t *next_srv = (next_srv_t*)ep->data;
    if (!next_srv) {
        error("next_srv is NULL\n");
        return 1;
    }
    
    q = next_srv->messages;   
    while (q != NULL) {
        len += sizeof(message_t);
        if (MSG_INPUT == q->msg.type) { 
            len += q->msg.inlen_fail;
        }
        q = q->next;
    }
    if (!len) {
        return 0;
    }

#ifdef MSG_FLOW
info("   [p%"PRIu32"] sending pending messages (%"PRIu32" bytes)\n",
        next_srv->sid, len);
#endif    
//info_wtime("pending messages -> p%"PRIu32":", next_srv->sid);

    sh_buf = (shared_buf_t*)malloc(sizeof(shared_buf_t) + len);
    if (NULL == sh_buf) {
        error("malloc (%s)\n", strerror(errno));
        return 1;
    }
    sh_buf->shared_count = 0;
    sh_buf->len = len;
    buf = sh_buf->buf;
    
    q = next_srv->messages;   
    while (q != NULL) {
        memcpy(buf, &q->msg, sizeof(message_t));
        buf += sizeof(message_t);
        if (MSG_INPUT == q->msg.type) {
//            info(" m%"PRIu32"/p%"PRIu32";", q->msg.owner, q->from_sid);
            if (0 != q->msg.inlen_fail) {
                memcpy(buf, q->msg.input, q->msg.inlen_fail);
                buf += q->msg.inlen_fail;
            }
        }
        q = q->next;
    }
//info("\n");    
#ifdef MSG_FLOW            
//dump_bytes(sh_buf->buf, sh_buf->len, "SEND_DATA");
#endif
    
    rv = ac_net_mod->isend(ep, sh_buf);
    if (rv) {
        error("malloc (%s)\n", strerror(errno));
        goto cleanup;
    }
    
    /* Remove messages */
    while ((q = next_srv->messages) != NULL) { 
        next_srv->messages = q->next;
        free(q); 
    }    
    rv = 0;
cleanup:
    if (0 == sh_buf->shared_count) {
        free(sh_buf);
    }
    
    return rv;
}

/**
 * Handle prematurely received messages
 */
//#define HPM_PRINT
int handle_premature_messages(message_queue_t **mq_ptr, 
                              uint64_t sqn,
                              message_handler_t mh)
{
    message_queue_t *mq, *q, *prev = NULL;
    srv_t *srv;
    int rv;
    uint32_t idx, degree_plus_one;    
    
    degree_plus_one = data.G[data.activeG]->degree + 1;

#ifdef HPM_PRINT    
info_wtime("Check list of premature messages for SQN=%"PRIu64"\n", sqn);
#endif
    
    mq = *mq_ptr;
    while ((q = mq) != NULL) {
#ifdef HPM_PRINT    
info("#### m%"PRIu32"; sqn=%"PRIu64"; from=p%"PRIu32" -- ", q->msg.owner, q->msg.sqn, q->from_sid);
#endif
        mq = q->next;
        if (0 == q->completed) {
#ifdef HPM_PRINT    
info("not completed\n");
#endif
            goto next_message;
        }
        if (q->msg.sqn < sqn) {
#ifdef HPM_PRINT    
info("outdated\n");
#endif
            goto remove_message;
        }
        if (q->msg.sqn > sqn) {
#ifdef HPM_PRINT    
info("premature\n");
#endif
            goto next_message;
        }
        if (MSG_INPUT == q->msg.type) {
            /* INPUT message for this round of consensus */
            idx = q->msg.owner * degree_plus_one;
            if (0 != data.sent_msgs[idx]) {
                /* INPUT already handled; remove it from the list */
#ifdef HPM_PRINT    
info("already delivered\n");
#endif
                goto remove_message;
            }
#ifdef HPM_PRINT    
info("deliver\n");
#endif
            /* Copy INPUT into server's buffer */
            if (0 != q->msg.inlen_fail) {
                srv = &data.vertex_to_srv_map[q->msg.owner];
                if (q->msg.inlen_fail != srv->inlen) 
                {
                    /* Reallocate space for input */
                    srv->input = realloc(srv->input, q->msg.inlen_fail);
                    if (NULL == srv->input) {
                        error("cannot allocate input space\n");
                        return 1;
                    }
                    srv->inlen = q->msg.inlen_fail;     
                }
                memcpy(srv->input, q->msg.input, q->msg.inlen_fail);
                set(&srv->state, SRV_INPUT);
            }
            mh(&q->msg, q->from_sid);
            goto remove_message;
        }
        else if (MSG_FAIL == q->msg.type) {
            /* FAIL notification for this round of consensus */
            mh(&q->msg, q->from_sid);
            goto remove_message;
        }
next_message:        
        prev = q;
        continue;
        
remove_message:
        if (NULL == prev) {
            *mq_ptr = q->next;
        }
        else {
            prev->next = q->next;
        }
        free(q);
    }
    return 0;
}


#endif

/* ================================================================== */
/* Local functions */
#if 1

#endif

