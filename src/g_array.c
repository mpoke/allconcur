/**
 * AllConcur                                                                                               
 * 
 * Tracking digraphs
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdio.h>
#include <stdlib.h>
 
#include <debug.h>
 
#include <digraph.h>
#include <g_array.h>

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

static g_successor_t*
successor_add(g_successor_t **successors, g_server_t *srv);
static void 
successor_rm(g_successor_t **successors, g_server_t *srv);
static void
successor_rm_all(g_successor_t **successors);
static int 
successor_search(g_successor_t *successors, g_server_t *srv);

static void 
g_successor_rm_all(g_array_entry_t *ge, g_server_t *srv);
static void 
g_bfs(g_array_entry_t *ge);

static void 
g_print(g_array_entry_t *ge);
static void 
g_free(g_array_entry_t *ge);

#endif

/* ================================================================== */
/* Global functions */
#if 1

/**
 * Add a new digraph to the array of digraphs 
 * => the server with ID sid failed and its input was not received yet
 */
g_array_t* g_array_entry_add(g_array_t **g_array, uint32_t sid)
{
    g_array_t *ga = NULL;
    
    if (NULL == *g_array) {
        /* Empty array */
        ga = (g_array_t*)malloc(sizeof(g_array_t));
        if (NULL == ga) {
            info("Error: cannot allocate g digraph\n");
            return NULL;
        }
        ga->next = NULL;
        ga->ge.g = RB_ROOT;
        ga->ge.self = sid;
        g_server_insert(&ga->ge, sid);
        ga->ge.modified = 0;
        *g_array = ga;
        return ga;
    }
    
    /* Search for g[sid] in array */
    ga = *g_array;
    while (ga != NULL) {
        if (ga->ge.self == sid) {
            /* g[sid] already in the array */
            return ga;
        }
        ga = ga->next;
    }
    
    /* Add g[sid] to the array */
    ga = (g_array_t*)malloc(sizeof(g_array_t));
    if (NULL == ga) {
        info("Error: cannot allocate g_array entry\n");
        return NULL;
    }
    ga->next = *g_array;
    ga->ge.g = RB_ROOT;
    ga->ge.self = sid;
    g_server_insert(&ga->ge, sid);
    ga->ge.modified = 0;
    *g_array = ga;
    return ga;
}

/**
 * Remove a digraph from the array of digraphs
 * => no more suspicion regarding the whereabout of the input 
 */
void g_array_entry_rm(g_array_t **g_array, uint32_t sid)
{
    g_array_t *ga = NULL, *gaaux = NULL;
    
    if (*g_array == NULL) return;
    
    ga = *g_array;
    if (ga->ge.self == sid) {
        /* Remove list head */
        *g_array = ga->next;
        g_free(&ga->ge);
        free(ga);
    }
    else for (; ga->next != NULL; ga = ga->next) {
        if (ga->next->ge.self == sid) {
            /* Must remove ga->next */
            gaaux = ga->next;
            ga->next = gaaux->next;
            g_free(&gaaux->ge);
            free(gaaux);
            break;
        }
    }
}

void g_array_free(g_array_t *g_array)
{
    g_array_t *ga;
    while ((ga = g_array) != NULL) {
        g_array = ga->next;
        g_free(&ga->ge);
        free(ga);
    }
}

void g_array_print(g_array_t *g_array)
{
    info(">>> Array of digraphs <<<\n");
    while (g_array != NULL) {
        info("   g[x%"PRIu32"]: ", g_array->ge.self);
        g_print(&g_array->ge);
        g_array = g_array->next;
    }
    info(".........................\n");
}

/**
 * Find a server with ID sid in a digraph
 */
g_server_t* g_server_search(g_array_entry_t *ge, uint32_t sid)
{
    struct rb_node *node = ge->g.rb_node;

    while (node) {
        g_server_t *srv = container_of(node, g_server_t, node);
		
        if (sid < srv->sid) {
            node = node->rb_left;
        }
        else if (sid > srv->sid) {
            node = node->rb_right;
        }
        else {
            return srv;
        }
    }
    return NULL;
}

/**
 * Search for an already failed server with no successors
 */
g_server_t* g_server_cond_search(g_array_entry_t *ge,
                                 g_server_is_failed is_failed)
{
    struct rb_node *node;
    g_server_t *srv;
    
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        srv = rb_entry(node, g_server_t, node);
        if (NULL != srv->successors) continue;
        if (is_failed(srv->sid)) return srv;
    }
    return NULL;
}

/**
 * Search for an already failed server with no successors
 */
int g_server_all_failed(g_array_entry_t *ge,
                        g_server_is_failed is_failed)
{
    struct rb_node *node;
    g_server_t *srv;
    
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        srv = rb_entry(node, g_server_t, node);
        if (!is_failed(srv->sid)) return 0;
    }
    return 1;
}

/**
 * Search for server with no successors for which there is no
 * path from the root of the digraph ge->g
 */
g_server_t* g_server_no_path_search(g_array_entry_t *ge)
{   
    struct rb_node *node;
    g_server_t *srv;
    
    g_bfs(ge);
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        srv = rb_entry(node, g_server_t, node);
        if (0 == srv->connected) return srv;
    }
    return NULL;
}

/**
 * Insert a server with ID sid in a digraph
 */
g_server_t* g_server_insert(g_array_entry_t *ge, uint32_t sid)
{
    g_server_t *srv;
    struct rb_node **new = &(ge->g.rb_node), *parent = NULL;
    
    while (*new) 
    {
        g_server_t *this = container_of(*new, g_server_t, node);
        
        parent = *new;
        if (sid < this->sid) {
            new = &((*new)->rb_left);
        }
        else if (sid > this->sid) {
            new = &((*new)->rb_right);
        }
        else {
            return NULL;
        }
    }
    
    /* Create new g_server_t structure */
    srv = (g_server_t*)malloc(sizeof(g_server_t));
    srv->sid = sid;
    srv->successors = NULL;
    if (ge->self == sid) 
        srv->connected = 1;
    else
        srv->connected = 0;

    /* Add new node and rebalance tree. */
    rb_link_node(&srv->node, parent, new);
    rb_insert_color(&srv->node, &ge->g);

    return srv;
}

/**
 * Remove a server from a digraph
 */
void g_server_rm(g_array_entry_t *ge, g_server_t *srv)
{
    if (NULL == srv) return;
    
    rb_erase(&srv->node, &ge->g);
    
    /* Remove own successor list */
    successor_rm_all(&srv->successors);
    
    /* Remove this server from the successors of other servers */
    g_successor_rm_all(ge, srv);
    
    /* Free g_server_t structure */
    free(srv);
    
    /* The removal of a server may leads to the disconnection of 
       other servers; hence, BFS is required */
    ge->modified = 1;
}

/**
 * Add a successor to the server with ID sid
 */
int g_successor_add(g_array_entry_t *ge, uint32_t sid, g_server_t *srv)
{
    g_server_t *predecessor;
    
    if (NULL == srv) {
        error("srv == NULL\n");
        return 1;
    }
       
    predecessor = g_server_search(ge, sid);
    if (NULL == predecessor) {
        error("no predecessor with sid=%"PRIu32"\n", sid);
        return 1;
    }
    
    
    if (NULL == successor_add(&predecessor->successors, srv)) {
        error("cannot add successor\n");
        return 1;
    }
    if (1 == predecessor->connected) {
        srv->connected = 1;
    }
    return 0;
}

/**
 * Remove server with ID sid as a server's successor
 */
void g_successor_rm(g_array_entry_t *ge, g_server_t *srv, uint32_t sid)
{
    g_server_t *successor;
    
    if (NULL == srv) return;
    
    successor = g_server_search(ge, sid);
    if (NULL == successor) return;
    
    successor_rm(&srv->successors, successor);
    
    /* The removal of a successor may leads to the disconnection of 
       some servers; hence, BFS is required */
    ge->modified = 1;
}

/**
 * Check whether a server has successors in the digraph
 */
int g_server_has_successors(g_array_entry_t *ge, g_server_t *srv)
{
    if (NULL == srv) return 0;    
    return (NULL != srv->successors);
}

/**
 * Check whether server with ID sid is the successor of a server
 */
int g_server_is_successor_of(g_array_entry_t *ge, 
                             uint32_t sid,
                             g_server_t *srv)
{
    g_server_t *successor;
    
    if (NULL == srv) return 0;
    
    successor = g_server_search(ge, sid);
    if (NULL == successor) return 0;
    
    return successor_search(srv->successors, successor);
}

/**
 * Check whether a digraph is empty 
 */
int g_is_empty(g_array_entry_t *ge)
{
    return (NULL == ge->g.rb_node);
}

#endif 

/* ================================================================== */
/* Local functions */
#if 1

/**
 * Add a successor to a list of successors 
 */
static g_successor_t*
successor_add(g_successor_t **successors, g_server_t *srv)
{
    g_successor_t *gs = NULL;
    
    if (NULL == *successors) {
        /* The list of successors is empty */
        gs = (g_successor_t*)malloc(sizeof(g_successor_t));
        if (NULL == gs) {
            info("Error: cannot allocate successor\n");
            return NULL;
        }
        gs->next = NULL;
        gs->srv = srv;
        *successors = gs;
        return gs;
    }
    
    /* Search for srv in list of successors */
    gs = *successors;
    while (gs != NULL) {
        if (gs->srv == srv) {
            /* srv already in the array */
            return gs;
        }
        gs = gs->next;
    }
    
    /* Add srv to the list of successors */
    gs = (g_successor_t*)malloc(sizeof(g_successor_t));
    if (NULL == gs) {
        info("Error: cannot allocate successor\n");
        return NULL;
    }
    gs->next = *successors;
    gs->srv = srv;
    *successors = gs;
    return gs;
}

/**
 * Remove a successor from a list of successors 
 */
static void 
successor_rm(g_successor_t **successors, g_server_t *srv)
{
    g_successor_t *gs = NULL, *gsaux = NULL;
    
    if (*successors == NULL) return;
    
    gs = *successors;
    if (gs->srv == srv) {
        /* Remove list head */
        *successors = gs->next;
        free(gs);
    }
    else for (; gs->next != NULL; gs = gs->next) {
        if (gs->next->srv == srv) {
            /* Must remove gs->next */
            gsaux = gs->next;
            gs->next = gsaux->next;
            free(gsaux);
            break;
        }
    }
}

static void
successor_rm_all(g_successor_t **successors)
{
    g_successor_t *gs;
    while ((gs = *successors) != NULL) {
        *successors = gs->next;
        free(gs);
    }
}

static int 
successor_search(g_successor_t *successors, g_server_t *srv)
{
    g_successor_t *gs;
    for (gs = successors; gs != NULL; gs = gs->next) {
        if (gs->srv == srv) return 1;
    }
    return 0;
}

static void 
g_successor_rm_all(g_array_entry_t *ge, g_server_t *srv)
{
    struct rb_node *node;
    g_server_t *other_srv;
    
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        other_srv = rb_entry(node, g_server_t, node);
        if (other_srv == srv) continue;
        successor_rm(&other_srv->successors, srv);
    }
}

/**
 * Find paths from ge->self to other servers in digraph ge->g
 */
static void 
g_bfs(g_array_entry_t *ge)
{
    struct rb_node *node;
    g_server_t *srv, **queue, **in, **out;
    g_successor_t *gs;
    
    /* Check whether BFS is necessary */
    if (0 == ge->modified) return;
    ge->modified = 0;
    
    /* Mark all nodes as disconnected */
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        srv = rb_entry(node, g_server_t, node);
        srv->connected = 0;
    }
    
    /* Find the root of the digraph */
    srv = g_server_search(ge, ge->self);
    srv->connected = 1;
    
    /* Init queue and add the root to it */
    queue = (g_server_t**)env.data;
    in = queue;
    *in = srv; out = in++;
    
    while (out < in) {
        srv = *(out++);
        for (gs = srv->successors; gs != NULL; gs = gs->next) {
            if (1 == gs->srv->connected) continue;
            gs->srv->connected = 1;
            *(in++) = gs->srv;
        } 
    }
}

static void g_print(g_array_entry_t *ge)
{
    struct rb_node *node;
    g_server_t *srv;
    g_successor_t *gs = NULL;
    
    for (node = rb_first(&ge->g); node; node = rb_next(node)) 
    {
        srv = rb_entry(node, g_server_t, node);
        info("p%"PRIu32"->(", srv->sid);
        for (gs = srv->successors; gs != NULL; gs = gs->next) {
            info(" p%"PRIu32, gs->srv->sid);
        }
        info(" ); ");
    }
    info("\n");
}

static void 
g_free(g_array_entry_t *ge)
{
    struct rb_node *node;
    g_server_t *srv;
    
    for (node = rb_first_postorder(&ge->g); node;) 
    {
        srv = rb_entry(node, g_server_t, node);
        node = rb_next_postorder(node);
        successor_rm_all(&srv->successors);
        free(srv);
    }
}

#endif

