/**                                                                                                      
 * AllConcur
 * 
 * KVS - Hash table
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>

#include <debug.h>
#include <kvs_ht.h>
#include <ac_types.h>

/* ================================================================== */
/* Type definitions */
#if 1

struct kvs_snapshot_entry_t {
    uint16_t   key_len;
    uint16_t   value_len;
    uint8_t    data[0];
};
typedef struct kvs_snapshot_entry_t kvs_snapshot_entry_t;

#endif 

/* ================================================================== */
/* Global variables */
#if 1

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static int
create_kvs_table(kvs_ht_t* kvs_ht);
static uint32_t 
hash(kvs_ht_t *kvs_ht, const char *key);
static kvs_list_t* 
lookup_key(kvs_ht_t *kvs_ht, const char *key);
static void 
remove_key(kvs_ht_t *kvs_ht, const char *key);
static int 
write_key(kvs_ht_t *kvs_ht, const char *key, kvs_blob_t *value);

#endif

/* ================================================================== */
/* Global functions */
#if 1

kvs_ht_t* create_kvs_ht(uint32_t size)
{

    int rc;
    kvs_ht_t *kvs_ht = NULL;
    
    if (0 == size) {
        size = DEFAULT_KVS_SIZE;
    }
    
    /* Allocate new KVS */
    kvs_ht = (kvs_ht_t*)malloc(sizeof(kvs_ht_t));
    if (NULL == kvs_ht) {
        error("Cannot allocate KVS hash table\n");
        return NULL;
    }
    
    /* Initiate KVS hash table */
    kvs_ht->size = size;
    rc = create_kvs_table(kvs_ht);
    if (0 != rc) {
        free(kvs_ht);
        kvs_ht = NULL;
        error("Cannot allocate KVS hash table\n");
        return NULL;
    }
    
    return kvs_ht;
}

/**
 *  Destroy the state machine 
 */
void destroy_kvs_ht(kvs_ht_t* kvs_ht)
{
    uint32_t i;
    kvs_list_t *list, *tmp;

    if (NULL == kvs_ht) {
        return;
    }
    if (NULL == kvs_ht->table) {
        free(kvs_ht);
        kvs_ht = NULL;
        return;
    }
    for (i = 0; i < kvs_ht->size; i++) {
        list = kvs_ht->table[i];
        while (NULL != list) {
            tmp = list;
            list = list->next;
            /* Free value */
            if (NULL != tmp->entry.value.data) {
                free(tmp->entry.value.data);
                tmp->entry.value.data = NULL;
            }
            /* Free key */
            if (NULL != tmp->entry.key) {
                free(tmp->entry.key);
                tmp->entry.key = NULL;
            }
            free(tmp);
        }
    }

    free(kvs_ht->table);
    kvs_ht->table = NULL;
    free(kvs_ht);
}

/** 
 * Apply a command to the state machine 
 */
int apply_kvs_ht_cmd(kvs_ht_t* kvs_ht,
                     uint8_t type, 
                     const char *key,
                     kvs_blob_t *value,
                     kvs_ht_reply_t **reply)
{
    int rc;
    kvs_list_t* list;
    
    if (NULL == kvs_ht) {
        error("SM is NULL\n");
        return 1;
    }
    if (NULL == key) {
        error("Key is NULL\n");
        return 1;
    }
    
    switch (type) {
        case KVS_PUT:
            if (NULL == value) {
                error("Value is NULL\n");
                return 1;
            }
//~ info("apply_kvs_ht_cmd: <%s:[%d bytes]>\n", key, value->len);              
            rc = write_key(kvs_ht, key, value);
            if (0 != rc) {               
                error("Cannot apply PUT operation\n");
                return 1;
            }
//~ print_kvs(kvs_ht);
            break;
        case KVS_GET:
            list = lookup_key(kvs_ht, key);
            if (NULL == list) {
                return 1;
            }
            else {
                *reply = (kvs_ht_reply_t*)
                        malloc(sizeof(kvs_ht_reply_t) + 
                                list->entry.value.len);
                (*reply)->len = list->entry.value.len;
                memcpy((*reply)->data, list->entry.value.data, 
                        (*reply)->len);
            }
            break;
        case KVS_RM:
            remove_key(kvs_ht, key);
            break;
        default:
            error("Unknown KVS command\n");
            return 1;
    }
    
    return 0;
}

int kvs_ht_get_uint64(kvs_ht_t* kvs_ht, 
                      const char *key, 
                      uint64_t *value)
{
    kvs_list_t* list;
    
    if (NULL == kvs_ht) {
        error("SM is NULL\n");
        return 1;
    }
    if (NULL == key) {
        error("Key is NULL\n");
        return 1;
    }
    list = lookup_key(kvs_ht, key);
    if (NULL == list) {
        return 1;
    }
    *value = *(uint64_t*)(list->entry.value.data);
    return 0;
}

/** 
 * Get the size (in bytes) of the state machine 
 */
uint32_t get_kvs_ht_bytes(kvs_ht_t *kvs_ht)
{
    if (!kvs_ht) return 0;
    return kvs_ht->bytes;
}

/** 
 * Make a snapshot of the state machine 
 */
void create_kvs_ht_snapshot(kvs_ht_t *kvs_ht, void *snapshot)
{
    uint32_t i;
    kvs_list_t *list;
    kvs_snapshot_entry_t *kvs_snapshot;
    uint8_t *ptr = (uint8_t*)snapshot;
    
    if (NULL == kvs_ht) {
        return;
    }
    if (NULL == kvs_ht->table) {
        return;
    }
//~ info_wtime("create_kvs_ht_snapshot\n");
    for (i = 0; i < kvs_ht->size; i++) {
        list = kvs_ht->table[i];
        while (NULL != list) {
            /* Copy entry to the snapshot */
//~ info("SM: <%s:[%d bytes]>\n", list->entry.key, list->entry.value.len);
            kvs_snapshot = (kvs_snapshot_entry_t*)ptr;
            kvs_snapshot->key_len = strlen(list->entry.key) + 1;
            kvs_snapshot->value_len = list->entry.value.len;
            ptr += sizeof(kvs_snapshot_entry_t);
            memcpy(ptr, list->entry.key, kvs_snapshot->key_len);
            ptr += kvs_snapshot->key_len;
            memcpy(ptr, list->entry.value.data, kvs_snapshot->value_len);
            ptr += kvs_snapshot->value_len;
            list = list->next;
//~ info("snapshot: <%s:[%d bytes]>\n", (char*)kvs_snapshot->data, kvs_snapshot->value_len);
        }
    }
}

/** 
 * Apply a snapshot to the state machine 
 */
int apply_kvs_snapshot(kvs_ht_t *kvs_ht, void *snapshot, uint32_t size)
{
    kvs_blob_t value;
    kvs_snapshot_entry_t *kvs_snapshot;
    uint8_t *ptr_end, *ptr;
    int rc;
    
    if (NULL == kvs_ht) {
        error("SM is NULL\n");
        return 1;
    }
    if (NULL == snapshot) {
        error("SM snapshot is NULL\n");
        return 1;
    }
    ptr = (uint8_t*)snapshot;
    
    ptr_end = ptr + size;
    while (ptr < ptr_end) {
        kvs_snapshot = (kvs_snapshot_entry_t*)ptr;
        value.len = kvs_snapshot->value_len;
        value.data = kvs_snapshot->data + kvs_snapshot->key_len;
//~ info("apply_kvs_snapshot -- write <%s:[%d]>\n", (char*)kvs_snapshot->data, value.len);
        rc = write_key(kvs_ht, (const char*)(kvs_snapshot->data), 
                        &value);
        if (0 != rc) {               
            error("Cannot apply snapshot\n");
            return 1;
        }
        ptr += sizeof(kvs_snapshot_entry_t) + kvs_snapshot->key_len 
                        + kvs_snapshot->value_len;
    }
    
    return 0;
}

void print_kvs(kvs_ht_t *kvs_ht)
{
    uint32_t i;
    kvs_list_t *list;
    
    if (NULL == kvs_ht) {
        info_wtime("KVS: empty\n");
        return;
    }
    if (NULL == kvs_ht->table) {
        info_wtime("KVS: empty\n");
        return;
    }
    info_wtime("KVS:\n");
    for (i = 0; i < kvs_ht->size; i++) {
        list = kvs_ht->table[i];
        while (NULL != list) {
            if (strncmp(list->entry.key, "srv#", 4) == 0) {
                srv_value_t *value = (srv_value_t*)list->entry.value.data;
                info("   <%s:[%s:%s]> %s\n", 
                        list->entry.key, value->ni.host, value->ni.ac_port,
                        (value->failed ? "OFF" : "ON"));

            }
            else
                info("   <%s:[%d bytes]>\n", 
                    list->entry.key, list->entry.value.len);
            list = list->next;
        }
    }
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static int
create_kvs_table(kvs_ht_t* kvs_ht)
{    
    kvs_ht->table = (kvs_list_t**)
                    malloc(sizeof(kvs_list_t*) * kvs_ht->size);
    if (NULL == kvs_ht->table) {
        error("Cannot allocate KVS hash table\n");
        return 1;
    }
    memset(kvs_ht->table, 0, sizeof(kvs_list_t*) * kvs_ht->size);
    
    return 0;
}

/**
 * Simple hash function
 */
static uint32_t 
hash(kvs_ht_t *kvs_ht, const char *key)
{
    uint32_t hashval;
    
    hashval = 0;
    for(; *key != '\0'; key++) {
        hashval = *key + (hashval << 5) - hashval;
    }
    return hashval % kvs_ht->size;
}

/**
 * Lookup function
 */
static kvs_list_t* 
lookup_key(kvs_ht_t *kvs_ht, const char *key)
{
    kvs_list_t *list;
    uint32_t hashval = hash(kvs_ht, key);

    for (list = kvs_ht->table[hashval]; list != NULL; 
            list = list->next) 
    {
        if (strcmp(key, list->entry.key) == 0) {
            return list;
        }
    }
    return NULL;
}

/**
 * Remove function
 */
static void 
remove_key(kvs_ht_t *kvs_ht, const char *key)
{
    kvs_list_t *list, *prev;
    uint32_t hashval = hash(kvs_ht, key);
    
    list = kvs_ht->table[hashval];
    if (list == NULL) return;
    if (strcmp(key, list->entry.key) == 0) {
        kvs_ht->table[hashval] = list->next;
        /* Update KVS size */
        kvs_ht->bytes = kvs_ht->bytes - sizeof(kvs_snapshot_entry_t) 
                - list->entry.value.len - strlen(list->entry.key) - 1;
        /* Remove entry */
        if (NULL != list->entry.value.data) {
            free(list->entry.value.data);
            list->entry.value.data = NULL;
        }
        free(list);
        return;
    }
    prev = list;
    for(list = list->next; list != NULL; list = list->next) {
        if (strcmp(key, list->entry.key) == 0) {
            prev->next = list->next;
            /* Update KVS size */
            kvs_ht->bytes = kvs_ht->bytes - sizeof(kvs_snapshot_entry_t) 
                - list->entry.value.len - strlen(list->entry.key) - 1;
            /* Remove entry */
            if (NULL != list->entry.value.data) {
                free(list->entry.value.data);
                list->entry.value.data = NULL;
            }
            free(list);
            return;
        }
        prev = list;
    }
}

/**
 * Update function
 */
static int 
write_key(kvs_ht_t *kvs_ht, const char *key, kvs_blob_t *value)
{
    kvs_list_t *list = NULL;
    unsigned int hashval;
    
    /* Search for list entry with this key */
    list = lookup_key(kvs_ht, key);
    if (NULL != list) {
        /* Key already exists - overwrite */
        if (list->entry.value.len != value->len) {
            /* Update KVS size */
            kvs_ht->bytes += value->len - list->entry.value.len;
            
            /* Resize blob */
            list->entry.value.len = value->len;
            
            /* Reallocate memory for the value */
            list->entry.value.data = 
                            realloc(list->entry.value.data, value->len);
            if (NULL == list->entry.value.data) {
                error("Cannot allocate new KVS value: %s\n", 
                                                    strerror(errno));
                return 1;
            }
        }
    }
    else {    
        /* Insert new key */
        hashval = hash(kvs_ht, key);
        list = (kvs_list_t*)malloc(sizeof(kvs_list_t));
        if (NULL == list) {
            error("Cannot allocate new KVS list\n");
            return 1;
        }
        
        /* Allocate memory for the key */
        list->entry.key = strdup(key);
        if (NULL == list->entry.key) {
            error("Cannot allocate new KVS key: %s\n", strerror(errno));
            return 1;
        }
        list->entry.value.len = value->len;
        
        /* Update KVS size */
        kvs_ht->bytes += sizeof(kvs_snapshot_entry_t) + value->len + 
                            strlen(key) + 1;

        /* Allocate memory for the value */
        list->entry.value.data = malloc(value->len);
        if (NULL == list->entry.value.data) {
            error("Cannot allocate new KVS value: %s\n", 
                                                    strerror(errno));
            return 1;
        }
        list->next = kvs_ht->table[hashval];
        kvs_ht->table[hashval] = list;
//~ info("write_key: new key = %s [%d bytes]\n", list->entry.key, strlen(key) + 1);
    }
    /* Copy value */
    memcpy(list->entry.value.data, value->data, value->len);

    return 0;
}

#endif
