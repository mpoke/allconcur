/**                                                                                                      
 * AllConcur
 * 
 * KVS - Hash table
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef KVS_HT_H
#define KVS_HT_H

#include <ac_ep.h>

#define DEFAULT_KVS_SIZE 1024

/* KVS commands */
#define KVS_PUT 1
#define KVS_GET 2
#define KVS_RM  3
#define CTRL_JOIN 4

#define REPLY_RC      0
#define REPLY_WIP     1
#define REPLY_FULL    2

struct kvs_blob_t {
    void        *data;
    uint16_t    len;
};
typedef struct kvs_blob_t kvs_blob_t;

struct kvs_entry_t {
    char *key;
    kvs_blob_t value;
};
typedef struct kvs_entry_t kvs_entry_t;

struct kvs_list_t {
    kvs_entry_t         entry;
    struct kvs_list_t   *next;
};
typedef struct kvs_list_t kvs_list_t;

struct kvs_ht_t {
    kvs_list_t  **table;
    uint32_t    size;
    uint32_t    bytes;
};
typedef struct kvs_ht_t kvs_ht_t;

kvs_ht_t* create_kvs_ht(uint32_t size);
void destroy_kvs_ht(kvs_ht_t* kvs_ht);
//~ int apply_kvs_ht_cmd(kvs_ht_t* kvs_ht, 
                     //~ kvs_ht_cmd_t *cmd, 
                     //~ kvs_ht_reply_t **reply);
int apply_kvs_ht_cmd(kvs_ht_t* kvs_ht,
                     uint8_t type, 
                     const char *key,
                     kvs_blob_t *value,
                     kvs_ht_reply_t **reply);
int kvs_ht_get_uint64(kvs_ht_t* kvs_ht, 
                      const char *key, 
                      uint64_t *value);                    
uint32_t get_kvs_ht_bytes(kvs_ht_t *kvs_ht);
void create_kvs_ht_snapshot(kvs_ht_t *kvs_ht, void *snapshot);
int apply_kvs_snapshot(kvs_ht_t *kvs_ht, void *snapshot, uint32_t size);
void print_kvs(kvs_ht_t *kvs_ht);


#endif /* KVS_HT_H */
