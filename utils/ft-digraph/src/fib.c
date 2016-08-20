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
 
#include <stdlib.h>
#include <limits.h>

#include <debug.h>
#include <digraph.h>
#include <fib.h>


/* ================================================================== */
/* Global variables */


/* ================================================================== */
/* Local functions - prototypes */

static inline fh_node_t*
fh_new_node(fibonacci_heap_t *fh, uint32_t idx);

static void
fh_insert_node(fibonacci_heap_t *fh, fh_node_t *node);
static inline void
fh_insert_root_list(fibonacci_heap_t *fh, fh_node_t *node);
static inline void
fh_insert_after(fh_node_t *a, fh_node_t *b);
static inline void
fh_remove_root_list(fibonacci_heap_t *fh, fh_node_t *node);
static inline void
fh_remove_node(fh_node_t *node);
static fh_node_t*
fh_extract_min_node(fibonacci_heap_t *fh);
static void
fh_consolidate(fibonacci_heap_t *fh);
static inline fh_node_t* 
fh_link_roots(fibonacci_heap_t *fh, fh_node_t *a, fh_node_t *b);
static void 
fh_cut_node(fibonacci_heap_t *fh, fh_node_t *node);

static void 
fh_print_children(fibonacci_heap_t *fh, fh_node_t *node, int level);

/* ================================================================== */
/* Fibonacci heap routines */
#if 1

/**
 * Initialize heap
 * @param fh heap pointer (already allocated)
 */
void fh_init_heap(fibonacci_heap_t *fh)
{
	fh->size = 0;
	fh->min = NULL;
	fh->root = NULL;
	fh->degree = (fh_node_t**)malloc((env.logN+1) * sizeof(fh_node_t*));
	fh->nodes = (fh_node_t*)malloc(env.N * sizeof(fh_node_t));
}

void fh_free_heap(fibonacci_heap_t *fh)
{
	if (fh->degree) {
		free(fh->degree);
		fh->degree = NULL;
	}
	if (fh->nodes) {
		free(fh->nodes);
		fh->nodes = NULL;
	}
}

/**
 * Empty heap
 */
void fh_emtpy(fibonacci_heap_t *fh)
{
	if (0 == fh->size) return;
	fh->size = 0;
	fh->root = NULL;
	fh->min = NULL;
	memset(fh->nodes, 0, env.N * sizeof(fh_node_t));
}

/**
 * Check whether the heap is empty
 */
int fh_is_empty(fibonacci_heap_t *fh) 
{
	return (fh->min == NULL);
}

/**
 * Insert new vertex into the heap
 */
void fh_insert(fibonacci_heap_t *fh, vertex_t data)
{
	fh_node_t *node = fh_new_node(fh, data.idx);
	node->data = data;
	
	fh_insert_node(fh, node);
	//~ printf("insert (%"PRIu32",%"PRIu32"): ", data.idx, data.d);fh_print_heap(fh);
}

fh_node_t* fh_get_node(fibonacci_heap_t *fh, uint32_t idx)
{
	return &(fh->nodes[idx]);
}

/**
 * Concatenate the root lists of two Fibonacci heaps
 */ 
fibonacci_heap_t* fh_union(fibonacci_heap_t *fha, fibonacci_heap_t *fhb)
{
	return NULL;
}

/**
 * Remove minimum from heap
 */
vertex_t fh_extract_min(fibonacci_heap_t *fh)
{
	fh_node_t *node;
	vertex_t v;
	v.idx = 0;
	v.d = UINT32_MAX;
		
	if (NULL != fh->min) {
		node = fh_extract_min_node(fh);
		v = node->data;
	}
	//~ printf("extract (%"PRIu32",%"PRIu32"): ", v.idx, v.d);fh_print_heap(fh);
	
	return v;
}

/**
 * Decrease the key (distance) of a node
 */
void fh_decrease_key(fibonacci_heap_t *fh, fh_node_t* node, uint32_t d)
{
	fh_node_t *p, *q;
	
	//~ printf("decrease (%"PRIu32",%"PRIu32") to %"PRIu32":", node->data.idx, node->data.d, d);
	node->data.d = d;
	
	p = node->parent;
	if (NULL != p) {
		if (p->data.d < d) return;
		/* The node is cut from the tree, joining the root list */ 
		//~ printf("before cut: ");fh_print_heap(fh);
		fh_cut_node(fh, node);
		//~ printf("after cut: ");fh_print_heap(fh);
		
		/* The parent of the node is cut if it is marked, 
		 * this continues for each ancestor until a parent that is not 
		 * marked is encountered, which is then marked. */
		while (NULL != (q = p->parent)) {
			if (!p->marked) {
				p->marked = 1;
				break;
			}
			fh_cut_node(fh, p);
			p = q;
		} 
	}
	
	/* If necessary, update min */
	if (d < fh->min->data.d) {
		fh->min = node;
	}
	//~ fh_print_heap(fh);
}

void fh_print_root_list(fibonacci_heap_t *fh)
{
	fh_node_t *p;
	printf("root-list %"PRIu32":%"PRIu32, fh->root->data.idx, fh->root->data.d);
    for (p = fh->root->next; p != fh->root; p = p->next) {
        printf(" %"PRIu32":%"PRIu32, p->data.idx, p->data.d);
    }
    printf("\n");
}

void fh_print_heap(fibonacci_heap_t *fh)
{
	fh_node_t *p;
	if (NULL == fh->root) {
		printf("empty heap\n"); return;
	}
	printf("heap %"PRIu32":%"PRIu32, fh->root->data.idx, fh->root->data.d);
	fh_print_children(fh, fh->root, 0);
    for (p = fh->root->next; p != fh->root; p = p->next) {
        printf(" %"PRIu32":%"PRIu32, p->data.idx, p->data.d);
        fh_print_children(fh, p, 0);
    }
    printf("\n");
    //~ if (NULL == fh->min) printf("\n");
    //~ else printf("\n   -> min=%"PRIu32":%"PRIu32"\n", fh->min->data.idx, fh->min->data.d);
}

#endif

/* ================================================================== */
/* Fibonacci heap node routines */
#if 1

static inline fh_node_t* 
fh_new_node(fibonacci_heap_t *fh, uint32_t idx)
{
	fh_node_t *node = &fh->nodes[idx];
	node->parent = NULL;
	node->child = NULL;
	node->prev = node;
	node->next = node;
	node->degree = 0;
	node->marked = 0;
	
	return node;
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static void
fh_insert_node(fibonacci_heap_t *fh, fh_node_t *node)
{	
	/* Create a new tree */
	fh_insert_root_list(fh, node);
	
	/* Adjust minimum */
	if (NULL == fh->min || (node->data.d < fh->min->data.d)) {
		fh->min = node;
	}
	
	/* Increase size */
	fh->size++;
}

static inline void
fh_insert_root_list(fibonacci_heap_t *fh, fh_node_t *node)
{
	if (NULL == fh->root) {
		/* No root */
		fh->root = node;
		node->prev = node;
		node->next = node;
		return;
	}

	fh_insert_after(fh->root->prev, node);
}

/**
 * Insert node b after node a
 */
static inline void
fh_insert_after(fh_node_t *a, fh_node_t *b)
{
	/* Link b with a->next to the right */
	b->next = a->next;
	/* Link a->next with b to the left */
	a->next->prev = b;
	/* Link b with a to the left */
	b->prev = a;
	/* Link a with b to the right */
	a->next = b;
}

static fh_node_t*
fh_extract_min_node(fibonacci_heap_t *fh)
{
	fh_node_t *min, *child, *p;
	int only_min = 0;
	
	/* It starts by removing the minimum node from the root list 
	 * and adding its children to the root list. */
	min = fh->min;
	if (min == min->next) only_min = 1;
	if ((child = min->child) != NULL) {
		child->prev->next = NULL;
		for (; child != NULL;) {
			p = child->next;
			child->parent = NULL;
			fh_insert_after(min, child);
			child = p;
		}
	}
	fh_remove_root_list(fh, min);
	fh->size--;
	//~ fh_print_root_list(fh);
	
	//~ printf("after removal (%d) ", fh->size); fh_print_heap(fh);
	
	/* Recompute the minimum and if needed consolidate */
	if (0 == fh->size) {
		/* The heap is empty */
		fh->min = NULL;
	}
	else if (only_min) {
		/* Heap min was the only node in the root list...
		 * Heap min <- the smallest node in the root list */
		fh->min = fh->root;
		for (p = fh->root->next; p != fh->root; p = p->next) {
			if (p->data.d < fh->min->data.d) {
				fh->min = p;
			}
		}
	}
	else {
		/* Consolidate */
		fh_consolidate(fh);
		
		//~ printf("after Consolidate:"); fh_print_heap(fh);
		
		/* Heap min <- the smallest node in the root list */
		fh->min = fh->root;
		for (p = fh->root->next; p != fh->root; p = p->next) {
			if (p->data.d < fh->min->data.d) {
				fh->min = p;
			}
		}
	}
	
	return min;
}

static inline void
fh_remove_root_list(fibonacci_heap_t *fh, fh_node_t *node)
{
	if (node->next == node) {
		/* The root list is empty */
		fh->root = NULL;
	}
	else {
		/* Remove node and update heap root */
		fh->root = node->next;
		fh_remove_node(node);
	}
}

static inline void
fh_remove_node(fh_node_t *node)
{
	struct fh_node_t *min, *p;

	/* Fix pointers */
	if (NULL != node->parent && (node->parent->child == node)) {
		/* Removed node is not a root -> adjust its parent child pointer
		 * Note: smallest among its siblings */
		if ((min = node->next) == node) {
			/* No other child */
			node->parent->child = NULL;
		}
		else {
			/* Find smallest child except "node" */
			for (p = min->next; p != node; p = p->next) {
				if (p->data.d < min->data.d) {
					min = p;
				}
			}
			node->parent->child = min;
		}
	}
	node->next->prev = node->prev; // link node's next to node's prev
	node->prev->next = node->next; // link node's prev to node's next
	node->parent = NULL;
	node->prev = node;
	node->next = node;
}

static void
fh_consolidate(fibonacci_heap_t *fh)
{
	uint32_t degree;
	fh_node_t *p, *q;
	
	memset(fh->degree, 0, (env.logN+1) * sizeof(fh_node_t*));
	
	//~ printf("consolidate:"); fh_print_heap(fh);
	
	p = fh->root;
	while (1) {
		//~ printf("p=%"PRIu32":%"PRIu32"\n", p->data.idx, p->data.d);
		degree = p->degree;
		if (NULL == fh->degree[degree]) {
			fh->degree[degree] = p;
			//~ printf("fh->degree[%"PRIu32"] = %"PRIu32":%"PRIu32"\n", degree, p->data.idx, p->data.d);
			p = p->next;
			continue;
		} 
		else if (p == fh->degree[degree]) {
			break;
		}
		
		//~ printf("link %"PRIu32":%"PRIu32" %"PRIu32":%"PRIu32"\n", 
			//~ p->data.idx, p->data.d, fh->degree[degree]->data.idx, 
			//~ fh->degree[degree]->data.d);
		
		
		/* Link together roots of the same degree */
		q = fh->degree[degree];
		p = fh_link_roots(fh, p, q);
		fh->degree[degree] = NULL;
		//~ printf("after link: "); fh_print_heap(fh);
	}
}

/**
 * Link two roots together; returns the parent
 */
static inline fh_node_t* 
fh_link_roots(fibonacci_heap_t *fh, fh_node_t *current, fh_node_t *prev)
{
	fh_node_t *x, *y;
	if (current->data.d > prev->data.d) {
		y = current; x = prev;
		if (x->next != y) {
			/* Move x after y */
			x->prev->next = x->next; // link x's prev to x's next
			x->next->prev = x->prev; // link x's next to x's prev
			fh_insert_after(y, x);
		}
	} else {
		x = current; y = prev;
	}
	/* Make sure the root is not y */
	fh->root = x;
		
	/* Remove node y... */
	y->prev->next = y->next; // link y's prev to y's next
	y->next->prev = y->prev; // link y's next to y's prev
	/* ...and add it as a child of node x */
	if (NULL == x->child) {
			x->child = y;
			y->prev = y;
			y->next = y;
	} else {
		fh_insert_after(x->child, y);
		if (x->child->data.d > y->data.d) {
			x->child = y;
		}
	}
	y->parent = x;
	x->degree++;
	
	return x;
}

static void 
fh_cut_node(fibonacci_heap_t *fh, fh_node_t *node)
{
	fh_node_t *parent = node->parent;
	fh_remove_node(node);
	parent->degree--;
	fh_insert_root_list(fh, node);
	node->parent = NULL;
	node->marked = 0;
}

static void 
fh_print_children(fibonacci_heap_t *fh, fh_node_t *node, int level)
{
	if (level > 7) exit(1);
	fh_node_t *p = node->child;
	if (NULL == p) return;
	printf("[%"PRIu32":%"PRIu32, p->data.idx, p->data.d);
	for (p = p->next; p != node->child; p = p->next) {
		printf(" %"PRIu32":%"PRIu32,  p->data.idx, p->data.d);
		fh_print_children(fh, p, level+1);
	}
	printf("]");
}

#endif
