/**                                                                                                      
 * AllConcur
 * 
 * Request pool (circular buffer)
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef REQUEST_POOL_H
#define REQUEST_POOL_H

#define RP_OK       0
#define RP_ERROR    1
#define RP_FULL     2

/* Size of request pool (in bytes) */
//~ #define REQ_POOL_SIZE 1048576 // 1 MB
#define REQ_POOL_SIZE 134217728 // 128 MB

#define MAX_MSG_SIZE 65536 // 64 kb

struct rp_reply_t {
    void *sm_data;
    uint8_t type;
    uint8_t rc;
};
typedef struct rp_reply_t rp_reply_t;


struct request_pool_t {
    uint8_t buffer[REQ_POOL_SIZE];
    pthread_mutex_t mutex;
    uint32_t in, out, len, wip_in;
    uint8_t empty;
};
typedef struct request_pool_t request_pool_t;


void rp_init(request_pool_t *rp);
void rp_destroy(request_pool_t *rp);
int rp_add_request(request_pool_t *rp, 
                    void *hdr, 
                    uint32_t hdr_len,
                    void *data,
                    uint32_t data_len,
                    uint32_t *in);
uint32_t rp_pack_requests(request_pool_t *rp, 
                          void **buffer, 
                          uint32_t max_size);
uint32_t rp_find_in(request_pool_t *rp, uint32_t offset);
void rp_complete_requests(request_pool_t *rp, int remove);

#endif /* REQUEST_POOL_H */
