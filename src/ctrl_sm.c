/**                                                                                                      
 * AllConcur
 * 
 * Control state machine
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>

#include <debug.h>

#include <kvs_ht.h>
#include <ac_types.h>
#include <ac_ep.h>
#include <ac_algorithm.h>
#include <allconcur.h>
#include <ctrl_sm.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define SRV_SQN_KEY "srv-sqn"

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

kvs_ht_t* new_ctrl_sm()
{
    kvs_ht_t *ctrl_sm = NULL;
    kvs_blob_t value;
    uint64_t sqn = 1; 
    int rc;
    
    ctrl_sm = create_kvs_ht(0);
    if (NULL == ctrl_sm) {
        error("cannot create control SM\n");
        return NULL;
    }
    
    /* Write srv-sqn:1 */   
    value.len = sizeof(uint64_t);
    value.data = &sqn;
    rc = apply_kvs_ht_cmd(ctrl_sm, KVS_PUT, SRV_SQN_KEY, &value, NULL);
    if (0 != rc) {
        error("cannot apply command to control SM\n");
        destroy_kvs_ht(ctrl_sm);
        return NULL;
    }
    
    return ctrl_sm;
}

uint64_t add_server_to_ctrl_sm(kvs_ht_t *ctrl_sm, srv_value_t *server)
{
    char srv_key[64];
    kvs_blob_t value;
    uint64_t sqn;
    int rc;
    
    /* Create new server unique key */
    rc = kvs_ht_get_uint64(ctrl_sm, SRV_SQN_KEY, &sqn);
    if (0 != rc) {
        error("cannot get %s\n", SRV_SQN_KEY);
        return 0;
    }
    sprintf(srv_key, "srv#%"PRIu64, sqn);
    
    /* Add server */
    value.len = sizeof(srv_value_t);
    value.data = server;
    rc = apply_kvs_ht_cmd(ctrl_sm, KVS_PUT, srv_key, &value, NULL);
    if (0 != rc) {
        error("cannot apply command to control SM\n");
        destroy_kvs_ht(ctrl_sm);
        return 0;
    }
    
    /* Update server SQN */
    sqn++;
    value.len = sizeof(uint64_t);
    value.data = &sqn;
    rc = apply_kvs_ht_cmd(ctrl_sm, KVS_PUT, SRV_SQN_KEY, &value, NULL);
    if (0 != rc) {
        error("cannot apply command to control SM\n");
        destroy_kvs_ht(ctrl_sm);
        return 0;
    }
    
    return sqn-1;
}

int remap_vertexes_to_servers(kvs_ht_t *ctrl_sm, 
                              srv_t *map, 
                              uint32_t n)
{
    uint32_t i, sid = 0;
    kvs_list_t *list;
    srv_value_t *value;
    char *word;
    char *key;

    if (NULL == ctrl_sm) {
        error("no ctrl_sm\n");
        return 1;
    }
    if (NULL == ctrl_sm->table) {
        error("no ctrl_sm->table\n");
        return 1;
    }
    for (i = 0; i < ctrl_sm->size; i++) {
        list = ctrl_sm->table[i];
        while (NULL != list) {
            if (strncmp(list->entry.key, "srv#", 4) == 0) {
                /* Server found */
                value = (srv_value_t*)list->entry.value.data;
                key = strdup(list->entry.key);
                word = strtok(key,"# \t\r\n");
                word = strtok(NULL, "# \t\r\n");
                map[sid].sqn = (uint64_t)atoll(word);
                map[sid].srv_value = value;
                if (map[sid].srv_value->failed) {
                    set(&map[sid].state, SRV_FAILED);
                }
                sid++;
                free(key);
            }
            list = list->next;
        }
    }
    return 0;
}

// TODO: prune CTRL SM -- removed failed servers

uint64_t add_client_to_ctrl_sm(kvs_ht_t *ctrl_sm, cid_t *cid)
{
    char clt_key[64];
    kvs_blob_t value;
    uint64_t sqn = 1;
    int rc;
    
    /* Create new client unique key */
    sprintf(clt_key, "clt#%"PRIu64"#%"PRIu64, 
                    cid->srv_sqn, cid->clt_sqn);
    
    /* Add client */
    value.len = sizeof(uint64_t);
    value.data = &sqn;
    rc = apply_kvs_ht_cmd(ctrl_sm, KVS_PUT, clt_key, &value, NULL);
    if (0 != rc) {
        error("cannot apply command to control SM\n");
        destroy_kvs_ht(ctrl_sm);
        return 0;
    }
    
    return sqn;
} 

uint64_t get_expected_sqn(kvs_ht_t *ctrl_sm, cid_t *cid)
{
    char clt_key[64];
    uint64_t sqn;
    int rc;
    
    /* Create client unique key */
    sprintf(clt_key, "clt#%"PRIu64"#%"PRIu64, 
                    cid->srv_sqn, cid->clt_sqn);
                    
    /* Get sqn */
    rc = kvs_ht_get_uint64(ctrl_sm, clt_key, &sqn);
    if (0 != rc) {
        return 0;
    }
    return sqn;
}

int update_expected_sqn(kvs_ht_t *ctrl_sm, cid_t *cid, uint64_t sqn)
{
    char clt_key[64];
    kvs_blob_t value;
    int rc;
    
    /* Create client unique key */
    sprintf(clt_key, "clt#%"PRIu64"#%"PRIu64, 
                    cid->srv_sqn, cid->clt_sqn);
                    
    /* Update expected SQN */
    value.len = sizeof(uint64_t);
    value.data = &sqn;
    rc = apply_kvs_ht_cmd(ctrl_sm, KVS_PUT, clt_key, &value, NULL);
    if (0 != rc) {
        error("cannot apply command to control SM\n");
        destroy_kvs_ht(ctrl_sm);
        return 1;
    }
    
    return 0;
}
                                   
#endif

/* ================================================================== */
/* Local functions */
#if 1

#endif
