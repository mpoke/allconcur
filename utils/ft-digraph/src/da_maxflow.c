/**                                                                                                      
 * Fault tolerant digraphs
 * 
 * Dinic's max-flow algorithm adapted for regular digraphs
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <debug.h>
#include <digraph.h>
#include <da_maxflow.h>

//~ #define DA_CIRCULANT  


/* ================================================================== */
/* Type definitions */
#if 1

struct da_flow_t {
    uint32_t degree;    /* number of offsets */
    uint8_t f[];    	/* skew-symmetric flow on each edge */
};
typedef struct da_flow_t da_flow_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

da_flow_t *F;

#endif
 
/* ================================================================== */
/* Local functions - prototypes */
#if 1

static inline void
new_flow();
static inline void
init_da(uint32_t degree);
static inline void 
add_flow(digraph_t *G, uint32_t u, uint32_t v);

static void 
BFS( digraph_t *G, 
     uint32_t s, 
     uint32_t t, 
     uint32_t *rank, 
     uint32_t *queue );
static uint8_t 
DFS( digraph_t *G, 
     uint32_t s, 
     uint32_t t, 
     uint32_t *rank,
     uint32_t *pred,
     uint32_t *stack );

#endif

/* ================================================================== */
/* Global functions */
#if 1

/**
 * Dinic's max-flow algorithm; implementation by Cherkassky
 * @return the s-t connectivity 
 */
void da_cherkassky(digraph_t *G, uint32_t s, uint32_t t)
{
    uint32_t i, k;
    uint32_t *rank, *pred, *queue_stack;
    
    /* Initialize environment / reset flow */
    init_da(G->degree);
    s += env.n; // out node
    
    /* Set buffers for BFS & DFS */
    rank = (uint32_t*)env.data;
    pred = rank + env.N;
    queue_stack = pred + env.N;
        
    while (1) {
        /* Construct layered network from residual graph */
        //~ for (i = 0; i < env.n; i++) {
			//~ for (k = 0; k < G->degree; k++) {
				//~ info ("(%d-%d):%d ", i, G->S[i*G->degree+k], F->f[env.n + i*G->degree+k]);
			//~ }
			//~ info("\n");
		//~ }
        BFS(G, s, t, rank, queue_stack);
        //~ info("BFS result: (%d,%d) \n", s, t);
        //~ for (i = 0; i < env.N; i++) {
            //~ if (rank[i] == env.N) info("(%d,x) ", i);
            //~ else info("(%d,%d) ", i, rank[i]);
        //~ }
        //~ info("\n");
        //~ for (i = 0; i < env.n; i++) {
			//~ for (k = 0; k < G->degree; k++) {
				//~ info ("(%d-%d):%d ", i, G->S[i*G->degree+k], F->f[env.n + i*G->degree+k]);
			//~ }
			//~ info("\n");
		//~ }
        if (rank[s] == env.N) {
            /* no more paths */
            break;
        }
        /* Find s-t paths in the layered network */
        while (1) {
            if (0 == DFS(G, s, t, rank, pred, queue_stack))
                break;
        }
        //~ info("\n");
    }
    
    k = 0; 
    for (i = 0; i < G->degree; i++) {
        if (0 != F->f[env.n + (s-env.n)*F->degree + i]) {
			k++;
		}
	}
	if (G->attrs.k > k) {
		G->attrs.k = k;
	}
}

/**
 * Free flow 
 */
void da_clean()
{
    if (F) {
		free(F);
		F = NULL;
	}
}

#endif 

/* ================================================================== */
/* Local functions */
#if 1


/**
 * Initialize the flow
 */
static inline void
new_flow()
{
    int i;
    if (F) free(F);
    F = (da_flow_t*)malloc(sizeof(da_flow_t) + env.n*env.n*sizeof(uint8_t));
    memset(F->f, 0, env.n*env.n*sizeof(uint8_t));
}

/**
 * Initialize DA environment
 */
static inline void
init_da(uint32_t degree)
{
    if (NULL == F) {
        new_flow();
        F->degree = degree;
    }
    else {
        F->degree = degree;
        memset(F->f, 0, env.n*(degree+1)*sizeof(uint8_t));
    }
}

/**
 * Add a flow of 1 on edge (u,v) 
 */
static inline void 
add_flow(digraph_t *G, uint32_t u, uint32_t v)
{
    uint32_t idx;
    
#if 0  /* This can never happen */  
    if (((u < env.n) && (v < env.n)) || 
        ((u >= env.n) && (v >= env.n))) 
    {
        /* There can be no flow on (u,v) */
        return;
    }
#endif     
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
#ifdef DA_CIRCULANT		
		if (G->circulant) {
			idx = G->inS[(v + env.N - u) % env.n];
		}
		else {
#endif
			idx = G->inS[(u-env.n)*env.n + v];
#ifdef DA_CIRCULANT			
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
#ifdef DA_CIRCULANT		
		if (G->circulant) {
			idx = G->inS[(u + env.N - v) % env.n];
		}
		else {
#endif
			idx = G->inS[(v-env.n)*env.n + u];
#ifdef DA_CIRCULANT			
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

/**
 * BFS from source s to target t (Construct layered network)
 */
static void 
BFS( digraph_t *G, 
     uint32_t s, 
     uint32_t t, 
     uint32_t *rank, 
     uint32_t *queue )
{
    uint32_t *in, *out;
    uint32_t i, j, u, v, offset;
    
    //~ info("start BFS %d-%d\n", s, t);
    
    /* Initialize arrays: 
     * rank is distance from u to t;
     * queue_stack is a queue */
    for (i = 0; i < env.N; i++) {
        rank[i] = env.N;
    }
    rank[t] = 0;
    /* Add t to queue */
    in = queue;
    *in = t; out = in++;
    while (out < in) {
        v = *(out++); 
        //~ info("   v=%d\n", v);
        if (v < env.n) {
            /* v is an in node */
            u = v + env.n; // out node of v
            /* (u,v)=(v_out, v_in) -> reverse edge (C(u,v) = 0) */
            if ( (rank[u] == env.N) && /* u not visited */
                 (1 == F->f[v]) )
            {
                /* F(u,v) = -1 (skew-symmetry) -> C-F > 0 */
                rank[u] = rank[v] + 1;
                //~ info("      u=%d (rev)\n", u);
                if (u == s) return;
                *(in++) = u;
            }
            for (i = 0; i < G->degree; i++) {
#ifdef DA_CIRCULANT				
				if (G->circulant) {
					u = (v + env.n - G->S[i]) % env.n; // in node
					u += env.n; // out node
					j = i;
				}
				else {
#endif					
					u = G->Nin[v*G->degree + i]; // in node
					for (j = 0; j < G->degree; j++) {
						if (v == G->S[u*G->degree + j]) break;
					}
					u += env.n; // out node
#ifdef DA_CIRCULANT					
				}
#endif				
                /* (u,v)=(u_out, v_in) -> normal edge (C(u,v) = 1) */
                if ( (rank[u] == env.N) && /* u not visited */
                     (0 == F->f[env.n + (u-env.n)*F->degree + j]) )
                {
                    /* F(u,v) = 0 -> C-F > 0 */
                    rank[u] = rank[v] + 1;
                    //~ info("      u=%d (flow on %d-%d: %d)\n", u, u-env.n, v, F->f[env.n + (u-env.n)*F->degree + j]);
                    if (u == s) {
						return;
					}
                    *(in++) = u;
                }
            }
        }
        /* Note: the source s is an out node */
        else {
            /* v is an out node */
            u = v - env.n; // in node of v
            /* (u,v)=(u_in, u_out) -> normal edge (C(u,v) = 1) */
            if ( (rank[u] == env.N) && /* u not visited */
                 (0 == F->f[u]) )
            {
                /* F(u,v) = 0 -> C-F > 0 */
                rank[u] = rank[v] + 1;
                *(in++) = u;
                //~ info("      u=%d\n", u);
            }
            for (i = 0; i < G->degree; i++) {
#ifdef DA_CIRCULANT				
				if (G->circulant) {
					u = (v + G->S[i]) % env.n; // in node 
				}
				else {
#endif					
					u = G->S[(v-env.n)*G->degree + i]; // in node
#ifdef DA_CIRCULANT					
				}
#endif				
                /* (u,v)=(v_in, u_out) -> reverse edge (C(u,v) = 0) */
                if ( (rank[u] == env.N) && /* u not visited */
                     (1 == F->f[env.n + (v-env.n)*F->degree + i]) )
                {
                    /* F(u,v) = -1 (skew-symmetry) -> C-F > 0 */
                    rank[u] = rank[v] + 1;
                    *(in++) = u;
                    //~ info("      u=%d (rev) (flow on %d-%d: %d)\n", u, v-env.n, u, F->f[env.n + (v-env.n)*F->degree + i]);
                }
            }
        }
    }
} 

/**
 * DFS from source s to target t (find augmenting path)
 */
static uint8_t 
DFS( digraph_t *G, 
     uint32_t s, 
     uint32_t t, 
     uint32_t *rank,
     uint32_t *pred,
     uint32_t *stack )
{
    uint32_t *top;
    uint32_t i, j, u, v;
    uint8_t ret = 0;
    
    //~ info("start DFS %d-%d\n", s, t);
    
    /* Initialize arrays: 
     * prev is array of parents;
     * queue_stack is a stack */
    for (i = 0; i < env.N; i++) {
        pred[i] = env.N;
    }
    /* Add s to the stack */
    top = stack;
    *(top++) = s;
    //~ print("%d %d\n", s, t);
    while (top != stack) {
        u = *(--top);
        //~ info("   u=%d\n", u);
        
        if (u < env.n) {
            /* u is an in node */
            v = u + env.n; // out node of u
            //~ info("      try v=%d\n", v);
            /* (u,v) = (u_in, u_out) -> normal edge (C(u,v) = 1) */
            if ( (rank[u] == rank[v] + 1) && (F->f[u] == 0) ) {
                /* F(u,v) = 0 -> C-F > 0 */
                pred[v] = u;
                *(top++) = v;
                //~ info("      v=%d\n", v);
            }
        }
        else {
            /* u is an out node */
            v = u - env.n; // in node of u; reverse edge
            //~ info("      try v=%d\n", v);
            /* (u,v) = (v_out, v_in) -> reverse edge (C(u,v) = 0) */
            if ( (rank[u] == rank[v] + 1) && (F->f[v] == 1) ) {
                /* F(u,v) = -1 (skew-symmetry) -> C-F > 0 */
                pred[v] = u;
                if (v == t) 
                    goto found_path;
                *(top++) = v;
                //~ info("      v=%d\n", v);
            }
        }
        if (u < env.n) {
            /* u is an in node */
            for (i = 0; i < G->degree; i++) {
#ifdef DA_CIRCULANT				
				if (G->circulant) {
					v = (u + env.n - G->S[i]) % env.n; // in node
					v += env.n; // out node
					j = i;
				}
				else {
#endif					
					v = G->Nin[u*G->degree + i]; // in node
					for (j = 0; j < G->degree; j++) {
						if (u == G->S[v*G->degree + j]) break;
					}
					v += env.n; // out node
#ifdef DA_CIRCULANT						
				}
#endif				
				//~ info("      try v=%d (%d) (flow on %d-%d: %d)\n", v, rank[u] - rank[v], v-env.n, u, F->f[env.n + (v-env.n)*F->degree + j]);
                /* (u,v) = (v_in, u_out) -> reverse edge (C(u,v) = 0) */
                if ( (rank[u] == rank[v] + 1) && 
                     (F->f[env.n + (v-env.n)*F->degree + j] == 1) )
                {
                    /* F(u,v) = -1 (skew-symmetry) -> C-F > 0 */
                    pred[v] = u;
                    *(top++) = v;
                    //~ info("      v=%d\n", v);
                }
            }            
        }
        else {
            /* u is an out node */
            for (i = 0; i < G->degree; i++) {
#ifdef DA_CIRCULANT				
				if (G->circulant) {
					v = (u + G->S[i]) % env.n; // in node
				}
				else {
#endif					
					v = G->S[(u-env.n)*G->degree + i]; // in node
#ifdef DA_CIRCULANT					
				}
#endif
				//~ info("      try v=%d (%d) (flow on %d-%d: %d)\n", v, rank[u] - rank[v], u-env.n, v, F->f[env.n + (u-env.n)*F->degree + i]);
                /* (u,v) = (u_out, v_in) -> normal edge (C(u,v) = 1) */
                if ( (rank[u] == rank[v] + 1) && 
                    (F->f[env.n + (u-env.n)*F->degree + i] == 0) )
                {
                    /* F(u,v) = 0 -> C-F > 0 */
                    pred[v] = u;
                    if (v == t) 
                        goto found_path;
                    *(top++) = v;
					//~ info("      v=%d\n", v);
                }
            }
        }
    }
    return 0;

found_path:
    /* Found augmenting path s-t */
    //~ info("!! found path\n");
    u = pred[t];
    v = t;
    //~ info("reversed path: %d ", v);
    /* Adapt flow */
    while (v != s) {
        //~ info("%d ", u);
        add_flow(G, u, v);
        v = u; 
        u = pred[u];
    }
    //~ info("\n");
    return 1;
}


#endif
