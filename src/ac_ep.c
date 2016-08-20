/**                                                                                                      
 * AllConcur
 * 
 * Endpoint
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
#include <stdlib.h>
#include <unistd.h>
#include <debug.h>

#include <allconcur.h>
#include <messages.h>
#include <ac_ep.h>

/* ================================================================== */
/* Type definitions */
#if 1

#endif

/* ================================================================== */
/* Global variables */
#if 1


#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1


#endif

/* ================================================================== */
/* Global functions */
#if 1

void ac_destroy_next_srv(void *next)
{
    next_srv_t *next_srv = (next_srv_t*)next;
    if (NULL == next) return;
    
    /* Destroy pending message queue */
    destroy_message_queue(&next_srv->messages);
    free(next_srv);
}

void ac_destroy_prev_srv(void *prev)
{
    prev_srv_t *prev_srv = (prev_srv_t*)prev;
    if (NULL == prev) return;
    
    /* prev->q is only a reference */
    if (NULL != prev_srv->input) {
        free(prev_srv->input);
        prev_srv->input = NULL;
    }
    if (prev_srv->ud_info.endpoint) {
        free(prev_srv->ud_info.endpoint);
        prev_srv->ud_info.endpoint = NULL;
    }
    free(prev_srv);
}

void ac_destroy_ac_srv(void *server)
{
    ac_srv_t *ac_srv = (ac_srv_t*)server;
    if (NULL == ac_srv) return;
    if (NULL != ac_srv->snapshot) {
        free(ac_srv->snapshot);
    }
    free(ac_srv);
}

void ac_destroy_client(void *clt)
{
    client_t *client = (client_t*)clt;
    if (NULL == clt) return;
    if (NULL != client->data) {
        free(client->data);
        client->data = NULL;
    }
    free(client);
}

#endif

/* ================================================================== */
/* Local functions */
#if 1


#endif
