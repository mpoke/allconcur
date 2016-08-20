/**                                                                                                      
 * Fault tolerant circulant digraphs
 * 
 * Successive Shortest Path algorithm -> MINIMUM COST FLOWS
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <limits.h>
#include <math.h>

#include <debug.h>
#include <digraph.h>
#include <fib.h>
#include <ssp.h>

#define SSP_REGULAR

/* ================================================================== */
/* Type definitions */
#if 1

struct ssp_flow_t {
    uint32_t degree;	/* number of offsets */
    uint8_t f[];     	/* skew-symmetric flow on each edge */
};
typedef struct ssp_flow_t ssp_flow_t;

#endif


/* ================================================================== */
/* Global variables */
#if 1

int heap_initialized;
fibonacci_heap_t fh;
ssp_flow_t *F;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
dijkstra( digraph_t *G, 
		  uint32_t s, 
		  uint32_t t, 
		  uint32_t *d, 
		  uint32_t *pred,
		  int *pi );
static inline void
new_flow();
static inline void
init_fh();
static inline void
init_ssp(uint32_t degree);
static inline void 
add_flow(digraph_t *G, uint32_t u, uint32_t v);

#endif

/* ================================================================== */
/* Global functions */
#if 1

/**
 * Min-sum disjoint path problem -> Successive Shortest Path (SSP)
 * Compute G->f+1 disjoint paths between two vertexes
 * s.t. the total length is minimized 
 */
void ssp(digraph_t *G, uint32_t s, uint32_t t)
{
	int *e, *pi;
	uint32_t *E, *topE, *D, *topD, *pred, *d;
	uint32_t i, j, k, u, v, len, DfL;
	size_t size;
	
	s += env.n; // s must be an out node
	
	/* Initialize environment / reset flow */
    init_ssp(G->degree);
    
    /* Initialize imbalance & potential */
    e = (int*)env.data;
    pi = e + env.N;
    memset(e, 0, 2*env.N * sizeof(int));
    e[s] = G->attrs.f + 1;
    e[t] = -e[s];   
    
    /* Initialize excess and deficit sets */
    E = (uint32_t*)(pi + env.N);
    topE = E;
    *(topE++) = s;
    D = E + env.N;
    topD = D;
    *(topD++) = t;
    
    /* Initialize arrays for Dijkstra algorithm */
    pred = D + env.N;
    d = pred + env.N;
       
	while (topE != E) {
		u = *(--topE);
		v = *(--topD);
		
		dijkstra(G, u, v, d, pred, pi);
		if (UINT32_MAX == d[v]) {
			/* Could not find path - this should never happen */
			info("Warning: not enough paths\n");
			exit(1);
		}
		/* Update imbalance */
		e[u]--; if (e[u] > 0) *(topE++) = u;
		e[v]++; if (e[v] < 0) *(topD++) = v;
		
		/* Update potentials... */
		for (i = 0; i < env.N; i++) {
			if (d[i] < d[v]) {
				/* ...for permanently labeled nodes */
				pi[i] = pi[i] - d[i] + d[v];
			}
		}
		
		/* Augment the flow along the shortest path */
		//~ printf("rpath: %d", v);
		while ((u = pred[v]) != UINT32_MAX) {
			/* Edge (u,v) on the path */
			//~ printf(" %"PRIu32, u);
			add_flow(G, u, v);
			v = u;
		}
		//~ printf("\n");
#if 0		
		printf("d:");
		for (i = 0; i < env.N; i++) {
			if (d[i] == UINT32_MAX) printf(" x");
			else printf(" %d", d[i]);
		}
		printf("\n");
		printf("pi:");
		for (i = 0; i < env.N; i++) {
			printf(" %d", pi[i]);
		}
		printf("\n");
#endif	
	}
	
	/* Compute maximum path length using the flow matrix */
	uint32_t *offset_idx = (uint32_t*)env.data; // store offset indexes
    uint32_t *summed_offset = offset_idx + env.N; // store combined offsets 
    uint8_t  *improved = (uint8_t*)(summed_offset + env.N); // flags for offset improvement
	//~ info("(s=%d, t=%d)\n", s-env.n,t);
	DfL = 0;
	for (i = 0; i < G->degree; i++) {
        if (0 == F->f[env.n + (s-env.n)*F->degree + i]) continue;
        u = s; // out node
#ifdef SSP_REGULAR        
        if (G->circulant) {
#endif			
			v = (s + G->S[i]) % env.n; // in node
			offset_idx[0] = i;
			summed_offset[0] = G->S[i];
#ifdef SSP_REGULAR			
		}
		else {
			v = G->S[(s-env.n)*G->degree + i]; // in node
		}
#endif		
        len = 1;
        //~ info("   path %d: %d", i+1, s-env.n);
        while (v != t) {
            //~ info("-%d", v);
            u = v+env.n; // out node
            for (j = 0; j < G->degree; j++) {
                if (1 == F->f[env.n + v*F->degree + j]) break;
            }
#ifdef SSP_REGULAR             
            if (G->circulant) {
#endif				
				v = (u + G->S[j]) % env.n; // in node
				offset_idx[len] = j;
				summed_offset[len] = G->S[j];
#ifdef SSP_REGULAR 				
			}
			else {
				v = G->S[(u-env.n)*G->degree + j]; // in node
			}
#endif			
            len++;
        }
        DfL += len;
        //~ info("-%d (%d)\n", v, len);
	
        if (len < G->attrs.DfU) continue;
        else if (len > G->attrs.DfU) {
			G->attrs.DfU = len;
			G->attrs.lpc = 1;
#ifdef SSP_REGULAR
			if (G->circulant) {
#endif				
				memset(G->freq, 0, G->degree*sizeof(uint32_t));
				memset(G->improve, 0, env.n*sizeof(uint32_t));
#ifdef SSP_REGULAR				
			}
#endif			
		}
		else {
			G->attrs.lpc++;
		}
#ifdef SSP_REGULAR
		if (!G->circulant) continue;
#endif			
		
		/* Compute frequency */
		for (k = 0; k < len; k++) {
			G->freq[offset_idx[k]]++;
		}
		
		/* Compute combined offsets and 
         * check what improvement they can bring */
        memset(improved, 0, env.n*sizeof(uint8_t));
        //~ printf("   [1]");
        //~ for (k = 0; k < len; k++) {
			//~ printf(" %d", summed_offset[k]);
		//~ }
		//~ printf("\n");
        for (k = 0; k < len; k++) {
            /* Offset sequences of length k+2  
             * -> reduces the path length with k+1 */
            //~ printf("   [%d]", k+2);
            for (j = k+1; j < len; j++) {
                summed_offset[j] = 
						summed_offset[j] + G->S[offset_idx[j-k-1]];
				if (summed_offset[j] > env.n) summed_offset[j] -= env.n;
				//~ printf(" %d", summed_offset[j]);
				improved[summed_offset[j]] |= 1;
            }
            //~ printf("\n");
        }
        /* Update local improve count */
        for (k = 0; k < env.n; k++) {
            if (improved[k]) G->improve[k]++;
        }
	}
	/* Compute lower bound for the fault diameter */
	DfL = ceil(1.*DfL/(G->attrs.f + 1)); 
	if (G->attrs.DfL < DfL) {
		G->attrs.DfL = DfL;
	}
}

/**
 * Find the length to the most distant vertex from a given root
 */
uint32_t largest_shorthest_path(digraph_t* G, uint32_t root)
{
	vertex_t v_data;
	uint32_t u, v, i, value;
	uint32_t *pred, *d;
	
	/* Initialize Fibonacci Heap */
    init_fh();
    
    /* Initialize arrays for Dijkstra algorithm */
    d = (uint32_t*)env.data;
    //~ pred = d + env.n;
    
    /* Reset heap & arrays */
	fh_emtpy(&fh);
	for (i = 0; i < env.N; i++) {
		d[i] = UINT32_MAX;
		//~ pred[i] = UINT32_MAX;
	}
	
	/* Initialize root s */
	d[root] = 0;
	v_data.idx = root; v_data.d = 0;
	fh_insert(&fh, v_data);
	
	while (1) {
		v_data = fh_extract_min(&fh);
		if (UINT32_MAX == v_data.d) break;
		u = v_data.idx;
		
		for (i = 0; i < G->degree; i++) {
			if (G->circulant) {
				v = (u + G->S[i])%env.n;
			}
			else {
				v = G->S[u*G->degree+i];
			}
			value = d[u] + 1;
			if (d[v] > value) {
				if (UINT32_MAX == d[v]) {
					d[v] = value; 
					//~ pred[v] = u;	
					v_data.idx = v; v_data.d = d[v];
					fh_insert(&fh, v_data);
				} else {
					d[v] = value; 
					//~ pred[v] = u;
					fh_decrease_key(&fh, fh_get_node(&fh, v), d[v]);
				}
			}
		}
	}
	
	value = d[0];
	for (i = 1; i < env.n; i++) {
		if (d[i] > value) value = d[i];
	}
	
	return value;
}

/**
 * Free SSP environment
 */
void ssp_clean()
{
    if (F) {
		free(F);
		F = NULL;
	}
    
    /* Free heap */
    fh_free_heap(&fh);
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

/**
 * Find shortest path between between two vertexes
 * Dijkstra algorithm with Fibonacci heap
 */
static void 
dijkstra( digraph_t *G, 
		  uint32_t s, 
		  uint32_t t, 
		  uint32_t *d, 
		  uint32_t *pred,
		  int *pi )
{
	vertex_t v_data;
	uint32_t u, v, i, j, value;
	
	/* Reset heap & arrays */
	fh_emtpy(&fh);
	for (i = 0; i < env.N; i++) {
		d[i] = UINT32_MAX;
		pred[i] = UINT32_MAX;
	}
	
//~ printf("\n############################\n");	
	/* Initialize root s */
	d[s] = 0;
	v_data.idx = s; v_data.d = 0;
	fh_insert(&fh, v_data);
	
	while (1) {
		v_data = fh_extract_min(&fh);
		if (UINT32_MAX == v_data.d) break;
		u = v_data.idx;
		
		if (u == t) break;
		
		if (u < env.n) {
			/* u - in node */
			v = u + env.n; // out node of u
			/* (u,v)=(u_in, u_out) -> normal edge (C(u,v) = 1) */
			if (0 == F->f[u]) { 
				/* Also edge in the residual graph
				 * Note: the residual graph contains only edges with a 
				 * positive residual capacity */
				value = d[u] + 1 + pi[v] - pi[u];
				if (d[v] > value) {
					if (UINT32_MAX == d[v]) {
						d[v] = value; pred[v] = u;	
						v_data.idx = v; v_data.d = d[v];
						fh_insert(&fh, v_data);
					} else {
						d[v] = value; pred[v] = u;
						fh_decrease_key(&fh, fh_get_node(&fh, v), d[v]);
					}
				}
			}	
			for (i = 0; i < G->degree; i++) {
#ifdef SSP_REGULAR				
				if (G->circulant) {
#endif					
					v = (u < G->S[i]) ? 
							(env.n + u) - G->S[i] : u - G->S[i]; // in node
					v += env.n; // out node
					j = i;
#ifdef SSP_REGULAR									
				}
				else {
					v = G->Nin[u*G->degree + i]; // in node
					for (j = 0; j < G->degree; j++) {
						if (u == G->S[v*G->degree + j]) break;
					}
					v += env.n; // out node
				}
#endif				
                /* (u,v)=(v_in, u_out) -> reverse edge (C(u,v) = 0) */
                if (1 == F->f[env.n + (v-env.n)*F->degree + j]) {
					/* Also edge in the residual graph
					 * Note: F(u,v) = -1 (skew-symmetry) -> C-F > 0 */
					value = d[u] + pi[v] - 1 - pi[u];
					if (d[v] > value) {
						if (UINT32_MAX == d[v]) {
							d[v] = value; pred[v] = u;	
							v_data.idx = v; v_data.d = d[v];
							fh_insert(&fh, v_data);
						} else {
							d[v] = value; pred[v] = u;
							fh_decrease_key(&fh, fh_get_node(&fh, v), d[v]);
						}
					}
				}
            }
		} else {
			/* u - out node */
			v = u - env.n; // in node of u
			//~ if (u == 16) printf("edge (%d,%d)\n", u, v);
			/* (u,v)=(u_out, u_in) -> reverse edge (C(u,v) = 0) */
			if (1 == F->f[v]) {
				/* Also edge in the residual graph
				 * Note: F(u,v) = -1 (skew-symmetry) -> C-F > 0 */		 
				value = d[u] + pi[v] - 1 - pi[u];
				if (d[v] > value) {
					if (UINT32_MAX == d[v]) {
						d[v] = value; pred[v] = u;	
						v_data.idx = v; v_data.d = d[v];
						fh_insert(&fh, v_data);
					} else {
						d[v] = value; pred[v] = u;
						fh_decrease_key(&fh, fh_get_node(&fh, v), d[v]);
					}
				}
			}
			for (i = 0; i < G->degree; i++) {
#ifdef SSP_REGULAR				
				if (G->circulant) {
#endif					
					v = u - env.n + G->S[i];
					if (v >= env.n) v -= env.n; // in node
#ifdef SSP_REGULAR					
				}
				else {
					v = G->S[(u-env.n)*G->degree + i]; // in node
				}
#endif				
                /* (u,v)=(u_out, v_in) -> normal edge (C(u,v) = 1) */
                if (0 == F->f[env.n + (u-env.n)*F->degree + i]) {
					/* Also edge in the residual graph */		
					value = d[u] + 1 + pi[v] - pi[u];
					//~ printf("value=%d d[v]=%d\n", value, d[v]);
					if (d[v] > value) {
						if (UINT32_MAX == d[v]) {
							d[v] = value; pred[v] = u;	
							v_data.idx = v; v_data.d = d[v];
							fh_insert(&fh, v_data);
						} else {
							d[v] = value; pred[v] = u;
							fh_decrease_key(&fh, fh_get_node(&fh, v), d[v]);
						}
					}
				}
			}
		}
	}
}
	

/**
 * Initialize flow
 */
static inline void
new_flow()
{
    int i;
    if (F) free(F);
    F = (ssp_flow_t*)malloc(sizeof(ssp_flow_t) + env.n*env.n*sizeof(uint8_t));
    memset(F->f, 0, env.n*env.n*sizeof(uint8_t));
}

/**
 * Initialize SSP environment
 */
static inline void
init_ssp(uint32_t degree)
{
    if (NULL == F) {
        new_flow();
        F->degree = degree;
    }
    else {
        F->degree = degree;
        memset(F->f, 0, env.n*(degree+1)*sizeof(uint8_t));
    }
    init_fh();
}

/**
 * Initialize Fibonacci Heap
 */
static inline void
init_fh()
{
    if (0 == heap_initialized) {
		fh_init_heap(&fh);
		heap_initialized = 1;
	}
}

/**
 * Add a flow of 1 on edge (u,v) 
 */
static inline void 
add_flow(digraph_t *G, uint32_t u, uint32_t v)
{
    uint32_t idx;
    
    if (v-u == env.n) {
        /* (u,v) is a direct edge between an in node and 
         * its corresponding out node 
         * (u,v) = (u_in, u_out) */
        F->f[u]++;
        return;
    }
    if (u-v == env.n) {
        /* (u,v) is a reverse edge between an out node and 
         * its corresponding in node 
         * (u,v) = (u_out, u_in) */
        F->f[v]--; /* skew-symmetry */
        return;
    }
    
    if (u >= env.n) {
#ifdef SSP_REGULAR
		if (G->circulant) {
#endif			
			idx = G->inS[(v + env.N - u) % env.n];
#ifdef SSP_REGULAR
		}
		else {
			idx = G->inS[(u-env.n)*env.n + v];
		}
#endif
		if (0 != idx) {
			/* (u,v) is a direct edge between an out node and an in node 
			 * (u,v) = (u_out, v_in) 
			 * Note: first, there are env.n in-out edges */
			F->f[env.n + (u-env.n)*F->degree + idx-1]++;
			return;
		}
	}
	if (v >= env.n) {
#ifdef SSP_REGULAR	
		if (G->circulant) {
#endif			
			idx = G->inS[(u + env.N - v) % env.n];
#ifdef SSP_REGULAR			
		}
		else {
			idx = G->inS[(v-env.n)*env.n + u];
		}
#endif		
		if (0 != idx) {
			/* (u,v) is a reverse edge between an in node and an out node 
			 * (u,v) = (v_in, u_out) */
			F->f[env.n + (v-env.n)*F->degree + idx-1]--;
			return;
		}
	}
}

#endif
