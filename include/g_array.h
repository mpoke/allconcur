/**
 * AllConcur                                                                                               
 * 
 * Tracking digraphs
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef G_ARRAY_H
#define G_ARRAY_H

#include <rbtree.h>


/* ================================================================== */

struct g_server_t;
struct g_successor_t {
    struct g_successor_t *next;
    struct g_server_t *srv;
};
typedef struct g_successor_t g_successor_t;

struct g_server_t {
    struct rb_node node;
    uint32_t sid;
    g_successor_t *successors;
    char connected;
};
typedef struct g_server_t g_server_t;

struct g_array_entry_t {
    struct rb_root g;
    uint32_t self;
    char modified;
};
typedef struct g_array_entry_t g_array_entry_t;

struct g_array_t {
    g_array_entry_t ge;
    struct g_array_t *next;
};
typedef struct g_array_t g_array_t;

typedef int (*g_server_is_failed)(uint32_t sid);

/* ================================================================== */

g_array_t* g_array_entry_add(g_array_t **g_array, uint32_t sid);
void g_array_entry_rm(g_array_t **g_array, uint32_t sid);
void g_array_free(g_array_t *g_array);
void g_array_print(g_array_t *g_array);

g_server_t* g_server_search(g_array_entry_t *ge, uint32_t sid);
g_server_t* g_server_cond_search(g_array_entry_t *ge,
                                 g_server_is_failed is_failed);
int g_server_all_failed(g_array_entry_t *ge,
                        g_server_is_failed is_failed);
g_server_t* g_server_no_path_search(g_array_entry_t *ge);
g_server_t* g_server_insert(g_array_entry_t *ge, uint32_t sid);
void g_server_rm(g_array_entry_t *ge, g_server_t *srv);
int g_successor_add(g_array_entry_t *ge, uint32_t sid, g_server_t *srv);
void g_successor_rm(g_array_entry_t *ge, g_server_t *srv, uint32_t sid);
int g_server_has_successors(g_array_entry_t *ge, g_server_t *srv);
int g_server_is_successor_of(g_array_entry_t *ge, 
                             uint32_t sid,
                             g_server_t *srv);
int g_is_empty(g_array_entry_t *ge);

#endif /* G_ARRAY_H */
