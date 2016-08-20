/**                                                                                                      
 * Fault tolerant digraphs
 * 
 * Regular digraphs
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef DIGRAPH_H
#define DIGRAPH_H

//~ #define STORE_PATHS

/* Environment where all digraphs have the same number of nodes */
struct digraph_env_t {
    uint32_t n, N, logN;     /* number of nodes */
    uint32_t nmax;
    uint32_t data_size;
    void *data;
};
typedef struct digraph_env_t digraph_env_t;
extern digraph_env_t env; 

struct digraph_attr_t {
    uint32_t f;         /* fault tolerance */
    uint32_t k;         /* connectivity */
    uint32_t D;			/* diameter */
    uint32_t DfU;       /* upper bound for the fault diameter */
    uint32_t DfL;       /* lower bound for the fault diameter */
    uint32_t lpc;  		/* longest path count */
};
typedef struct digraph_attr_t digraph_attr_t;

/* Digraph G = (N, V) */
struct digraph_t {
    digraph_attr_t attrs;
    uint32_t degree;    /* degree */
    uint32_t data_size; /* data size in bytes */
    uint32_t *S;		/* pointer to offsets / out-neighbors */
    uint32_t *inS;   	/* pointer to list of membership */
    uint32_t *Nin;		/* pointer to in-neighbors */
    uint32_t *inNin;   	/* pointer to list of in-neighbors membership */
    uint32_t *freq;     /* pointer to offset frequencies */
    uint32_t *improve;  /* pointer to a list of offset's improvement */
    uint8_t circulant;
    uint8_t data[];     /* data */
};
typedef struct digraph_t digraph_t;
typedef digraph_t circ_digraph_t;

/* Environment routines */
void init_digraph_env(uint32_t n);
void free_digraph_env();

/* Allocation routines */
digraph_t* new_digraph();
circ_digraph_t* new_circ_digraph();
circ_digraph_t* new_binomial_graph();
digraph_t* create_complete_digraph();
digraph_t* create_sim_digraph(uint32_t degree, uint32_t pivot);
void destroy_digraph(digraph_t **G);
void copy_digraph(digraph_t *src_G, digraph_t *dst_G);

/* Setters and getters */
void set_digraph_ft(digraph_t *G, uint32_t f);
uint32_t get_successor(digraph_t *G, uint32_t u, uint32_t idx);
uint32_t get_predecessor(digraph_t *G, uint32_t v, uint32_t idx);
uint32_t get_predecessor_idx(digraph_t *G, uint32_t v, uint32_t u);

/* Digraph generators */
void rand_digraph(digraph_t *G, uint32_t degree);
void rand_circ_digraph(circ_digraph_t *G, uint32_t degree);
int next_circ_digraph(circ_digraph_t *G, uint32_t degree);
uint32_t mutate_circ_digraph_rand(circ_digraph_t* G);
uint32_t mutate_circ_digraph_greedy(circ_digraph_t* G);
uint32_t mutate_circ_digraph_2phase(circ_digraph_t* G);
	int add_offset_rand(circ_digraph_t* G);
	int add_offset_greedy(circ_digraph_t* G);
	int rm_offset_rand(circ_digraph_t* G, int not_last);
	int rm_offset_greedy(circ_digraph_t* G, int not_last);
	
/* Connectivity and fault-diameter bounds */
void digraph_connectivity(digraph_t* G);
void digraph_diameter(digraph_t* G);
uint32_t min_diameter(uint32_t n, uint32_t degree);
uint32_t digraph_fault_diameter( digraph_t* G, 
                                 uint32_t ub_DfU, 
                                 uint32_t ub_lpc );

void print_digraph(digraph_t* G);
void digraph2dot(digraph_t* G, char *dot_file);
void graph2dot(digraph_t* G, char *dot_file);

#endif /* DIGRAPH_H */
