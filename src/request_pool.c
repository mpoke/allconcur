/**                                                                                                      
 * AllConcur
 * 
 * Request pool (circular buffer)
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

#include <debug.h>
#include <request_pool.h>

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

static int 
enough_space(request_pool_t *rp, uint32_t bytes);
static uint32_t 
add_before_end(request_pool_t *rp, void *req, uint32_t bytes);
static int 
add_before_out(request_pool_t *rp, void *req, uint32_t bytes);

#endif

/* ================================================================== */
/* Global functions */
#if 1

void rp_init(request_pool_t *rp)
{
    pthread_mutex_init(&rp->mutex, NULL);
    rp->in = 0;
    rp->out = 0;
    rp->wip_in = 0;
    rp->len = REQ_POOL_SIZE;
    rp->empty = 1;  
}

void rp_destroy(request_pool_t *rp)
{
    pthread_mutex_destroy(&rp->mutex);
}

int rp_is_empty(request_pool_t *rp) 
{
    return rp->empty;
}

/**
 * Adding a request to the pool
 * @param   rp request pool
 * @param   hdr the request header
 * @param   hdr_len header size
 * @param   data the request data
 * @param   data_len data size
 * @param   in the in index of this request
 */
int rp_add_request(request_pool_t *rp, 
                    void *hdr, 
                    uint32_t hdr_len,
                    void *data,
                    uint32_t data_len,
                    uint32_t *in)
{
    uint32_t remaining_bytes;
    uint32_t len = hdr_len + data_len;
    
//info("rp_add_request\n");
//info("   rp->out=%"PRIu32"; rp->in=%"PRIu32"; rp->wip_in=%"PRIu32"\n", 
//            rp->out, rp->in, rp->wip_in);
    /* Lock */
    pthread_mutex_lock(&rp->mutex);
    
    if (!enough_space(rp, len)) {
        info("Cannot fit %"PRIu32" bytes into the request pool (capacity=%"PRIu32")\n", 
                    len, rp->len);
        pthread_mutex_unlock(&rp->mutex);
        return RP_FULL;
    }
//info_wtime("Client request -- %d bytes\n", len);
    if (in) *in = rp->in;
    if (rp->empty) {
        /* Empty */
        rp->out = 0;
        rp->wip_in = 0;
        if (in) *in = 0;
        /* Add header */
        memcpy(rp->buffer, hdr, hdr_len);
        /* Add data */
        if (data_len) {
            memcpy(rp->buffer+hdr_len, data, data_len);
        }
        /* Advance in index */
        rp->in = len;
        rp->empty = 0;
    }
    else {
        if (rp->out < rp->in) {                 /* Not wrapped-around */
            /* Add header */
            remaining_bytes = add_before_end(rp, hdr, hdr_len);
            if (remaining_bytes > 0) {
                /* Header wraps around */
                add_before_out(rp, ((uint8_t*)hdr)+(hdr_len-remaining_bytes), 
                                        remaining_bytes);
                /* Add data */
                if (data_len) {
                    add_before_out(rp, data, data_len);
                }
            }
            else {
                /* Header does not wrap around -- add data */
                if (data_len) {
                    remaining_bytes = add_before_end(rp, data, data_len);
                    if (remaining_bytes > 0) {
                        /* Header wraps around */
                        add_before_out(rp, ((uint8_t*)data)+(data_len-remaining_bytes), 
                                            remaining_bytes);
                    }
                }
            }
        }
        else {                                      /* Wrapped around */
            /* Add header */
            add_before_out(rp, hdr, hdr_len);
            /* Add data */
            if (data_len) {
                add_before_out(rp, data, data_len);
            }
        }
    }
    
    /* Unlock */
    pthread_mutex_unlock(&rp->mutex);
 
#if 0
if (in) {    
    info("   rp->out=%"PRIu32"; rp->in=%"PRIu32"; rp->wip_in=%"PRIu32"; client->in=%"PRIu32"\n", 
            rp->out, rp->in, rp->wip_in, *in);
}
else {
    info("   rp->out=%"PRIu32"; rp->in=%"PRIu32"; rp->wip_in=%"PRIu32"\n", 
            rp->out, rp->in, rp->wip_in);
}
#endif 
    
    return RP_OK;
}

uint32_t rp_pack_requests(request_pool_t *rp, 
                          void **buffer, 
                          uint32_t max_size) 
{
    uint32_t len;
    
    if (rp->empty) {
        return 0;
    }
    
    /* Lock */
    pthread_mutex_lock(&rp->mutex);
    
    if (rp->empty) {
        //info("rp is EMPTY\n");
        pthread_mutex_unlock(&rp->mutex);
        return 0;
    }

    
    /* Mark WIP in index */
    rp->wip_in = rp->in;
    
    /* Reallocate buffer */
    if (rp->out < rp->in) {
        /* Normal */
        len = rp->in - rp->out;
    }
    else {
        /* Wrapped around */
        len = rp->len - rp->out + rp->in;
    }
    if (max_size) {
        if (len > max_size) {
            len = max_size;
        }
    }
//info("rp_pack_requests: %"PRIu32" bytes\n", len);
    *buffer = realloc(*buffer, len);
    /* Copy requests into buffer */
    if (rp->out < rp->in) {
        /* Normal */
        memcpy(*buffer, rp->buffer + rp->out, len);
    }
    else {
        if (max_size) {
            if (rp->len - rp->out < len) {
                memcpy(*buffer, rp->buffer + rp->out, len);
            }
            else {
                /* Wrapped around */
                memcpy(*buffer, rp->buffer + rp->out, rp->len - rp->out);
                memcpy(((uint8_t*)*buffer) + rp->len - rp->out, rp->buffer, 
                        len - (rp->len - rp->out));
            }
        }
        else {
            memcpy(*buffer, rp->buffer + rp->out, rp->len - rp->out);
            memcpy(((uint8_t*)*buffer) + rp->len - rp->out, rp->buffer, 
                        rp->in);
        }
    }
    
//info("   rp->out=%"PRIu32"; rp->in=%"PRIu32"; rp->wip_in=%"PRIu32"\n", 
//            rp->out, rp->in, rp->wip_in);
//~ info("   len =  %"PRIu32"\n", len);           
    
    /* Unlock */
    pthread_mutex_unlock(&rp->mutex);
 
    return len;
}

uint32_t rp_find_in(request_pool_t *rp, uint32_t offset)
{
    uint32_t in;

    /* Lock */
    pthread_mutex_lock(&rp->mutex);

    in = rp->out + offset;
    if (in >= rp->len) in -= rp->len;
//info("rp_find_in: offset=%"PRIu32", in=%"PRIu32"\n", offset, in);

    /* Unlock */
    pthread_mutex_unlock(&rp->mutex);

    return in;
}

void rp_complete_requests(request_pool_t *rp, int remove) 
{
    /* Lock */
    pthread_mutex_lock(&rp->mutex);
    
//info("rp_complete_requests\n");
    if (rp->empty) {
        //info("   rp empty\n");
        pthread_mutex_unlock(&rp->mutex);
        return;
    }
 
    if (rp->wip_in == rp->out) {
        /* No requests completed */
        //info("  no requests completed\n");
        pthread_mutex_unlock(&rp->mutex);
        return;
    }
    
    if (remove) {   
        rp->out = rp->wip_in;
        if (rp->in == rp->wip_in) {
            /* Request pool is empty */
            rp->empty = 1;
        }
    }
    else {
        rp->wip_in = rp->out;
    }
//info("   rp->out=%"PRIu32"; rp->in=%"PRIu32"; rp->wip_in=%"PRIu32"\n", 
    //            rp->out, rp->in, rp->wip_in);
    
    /* Unlock */
    pthread_mutex_unlock(&rp->mutex);
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static int 
enough_space(request_pool_t *rp, uint32_t bytes)
{
    uint32_t avail_bytes;
    
    if (rp->empty) {
        if (bytes > rp->len) {
            info("request larger than request pool\n");
            return 0;
        }
        return 1;
    }
    if (rp->out == rp->in) {
        info("request pool full\n");
        return 0;
    }
    if (rp->out < rp->in) {
        if (bytes > rp->len - rp->in + rp->out) {
            info("not enough space: needed=%"PRIu32"; available=%"PRIu32"\n", 
                            bytes, rp->len - rp->in + rp->out);
            return 0;
        }
        return 1;
    }
    if (bytes > rp->out - rp->in) {
        info("not enough space: needed=%"PRIu32"; available=%"PRIu32"\n", 
                    bytes, rp->out - rp->in);
        return 0;
    }
    return 1; 
}

static uint32_t 
add_before_end(request_pool_t *rp, void *req, uint32_t bytes)
{
    uint32_t avail_bytes;
       
    avail_bytes = rp->len - rp->in;
    if (bytes <= avail_bytes) {
        memcpy(rp->buffer + rp->in, req, bytes);
        rp->in += bytes;
        return 0;
    }
    else {
        memcpy(rp->buffer + rp->in, req, avail_bytes);
        rp->in = 0;
        return bytes - avail_bytes;
    }
}

static int 
add_before_out(request_pool_t *rp, void *req, uint32_t bytes)
{
    uint32_t avail_bytes;
    
    avail_bytes = rp->out - rp->in;
    if (bytes > avail_bytes) return 1;
    memcpy(rp->buffer + rp->in, req, bytes);
    rp->in += bytes;
    return 0;
}

#endif
