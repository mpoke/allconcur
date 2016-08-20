/**                                                                                                      
 * Fault tolerant circulant digraphs
 * 
 * Fibonacci heap storing vertexes (Dijkstra's algorithm)
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
 * 
 * Copyright (c) 1997-2003 John-Mark Gurney.
 *               All rights reserved. 
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 

#ifndef FIB_H
#define FIB_H

struct vertex_t {
	uint32_t idx;
	uint32_t d;	/* the distance (Dijkstra) */
};
typedef struct vertex_t vertex_t;

struct fh_node_t {
	struct fh_node_t *parent;
	struct fh_node_t *child;
	struct fh_node_t *prev;
	struct fh_node_t *next;
	vertex_t data;
	uint32_t degree;
	uint8_t marked;
};
typedef struct fh_node_t fh_node_t;

struct fibonacci_heap_t {
	fh_node_t *min;
    fh_node_t *root;
    fh_node_t **degree;
    fh_node_t *nodes;
    uint32_t size;
};
typedef struct fibonacci_heap_t fibonacci_heap_t;

void fh_init_heap(fibonacci_heap_t *fh);
void fh_free_heap(fibonacci_heap_t *fh);
void fh_emtpy(fibonacci_heap_t *fh);
int fh_is_empty(fibonacci_heap_t *fh);
void fh_insert(fibonacci_heap_t *fh, vertex_t data);
fh_node_t* fh_get_node(fibonacci_heap_t *fh, uint32_t idx);
fibonacci_heap_t* fh_union(fibonacci_heap_t *fha, fibonacci_heap_t *fhb);
vertex_t fh_extract_min(fibonacci_heap_t *fh);
void fh_decrease_key(fibonacci_heap_t *fh, fh_node_t* node, uint32_t d);

void fh_print_root_list(fibonacci_heap_t *fh);
void fh_print_heap(fibonacci_heap_t *fh);


#endif /* FIB_H */
