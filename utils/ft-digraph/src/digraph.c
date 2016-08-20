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
 
#include <stdlib.h>
#include <unistd.h>
#include <math.h>

#include <debug.h>
#include <digraph.h>
#include <ssp.h>
#include <da_maxflow.h>

/* ================================================================== */
/* Type definitions */
#if 1

/* Vertex label of a line digraph */
struct line_label_t {
	uint32_t u, v;
};
typedef struct line_label_t line_label_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

digraph_env_t env;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
circ_digraph_connectivity(circ_digraph_t* G);
static inline uint32_t
pow2roundup(uint32_t x);
static inline uint32_t
log2roundup(uint32_t x);

#endif

/* ================================================================== */
/* Global functions */
#if 1

/** 
 * Called every time n is modified
 */
void init_digraph_env(uint32_t n)
{
    if (env.n != n) {
        env.n = n;
        env.N = 2*n;
        env.logN = log2roundup(env.N);
        
        env.data_size = env.N*(4*sizeof(uint32_t) + 2*sizeof(int));
        env.data = realloc(env.data, env.data_size);
    }
}

void free_digraph_env()
{
	if (NULL != env.data) {
        free(env.data);
        env.data = NULL;
    }
}

/**
 * Create a new digraph of size env.n
 */
digraph_t* new_digraph()
{
	digraph_t *G = NULL;
	uint32_t data_size = 0;
	uint32_t n_sq = env.n * env.n;
    
    data_size += 2*n_sq;	// offsets for all vertexes
    data_size += 2*n_sq;	// offset membership
    data_size *= sizeof(uint32_t);
    
    G = (digraph_t*)malloc(sizeof(digraph_t) + data_size);
	memset(G->data, 0, data_size);
    G->data_size = data_size;
    G->S = (uint32_t*)G->data;
	G->inS = G->S + n_sq;
	G->Nin = G->inS + n_sq;
	G->inNin = G->Nin + n_sq;
	G->freq = NULL;
    G->improve = NULL;
    G->attrs.f = 0;
    G->attrs.k = 0;
    G->attrs.DfU = 0;
    G->attrs.DfL = 0;
    G->attrs.lpc = 0;
    G->degree = 0;
    G->circulant = 0;
    
    return G;
}

/**
 * Create a new circulant digraph of size env.n
 */
circ_digraph_t* new_circ_digraph()
{
    circ_digraph_t *G = NULL;
    uint32_t data_size = 0;
    
    data_size += env.n;          // offsets
    data_size += env.n;          // index in G->S
    data_size += env.n;          // list of offset frequencies
    data_size += env.n;          // list of improvements
    data_size *= sizeof(uint32_t);
     
    G = (circ_digraph_t*)malloc(sizeof(circ_digraph_t) + data_size);
    memset(G->data, 0, data_size);
    G->data_size = data_size;
    G->S = (uint32_t*)G->data;
	G->inS = G->S + env.n;
	G->Nin = NULL;
	G->inNin = NULL;
	G->freq = G->inS + env.n;
    G->improve = G->freq + env.n;
    G->attrs.f = 0;
    G->attrs.k = 0;
    G->attrs.DfU = 0;
    G->attrs.DfL = 0;
    G->attrs.lpc = 0;
    G->degree = 0;
    G->circulant = 1;
    
    return G;
}

/**
 * Generate binomial graph with env.n nodes
 * offsets: s = 2^j and s = env.n-2^j, for j <= log2(env.n)
 */
circ_digraph_t* new_binomial_graph()
{
    circ_digraph_t *G = new_circ_digraph();
    
    uint32_t i, offset, degree = 0, logn = floor(log2(env.n));
    
    //~ printf("logn = %d\n", logn);
    
    G->inS[1] = 1; G->S[0] = 1;degree++;
    G->inS[env.n-1] = 2; G->S[1] = env.n-1; degree++;
    offset = 1;
    for (i = 1; i <= logn; i++) {
        offset <<= 1;
        if (offset == env.n) break;
        if (0 == G->inS[offset]) {
            G->S[degree++] = offset;
            G->inS[offset] = degree;
        }
#if 1        
        if (0 == G->inS[env.n-offset]) {
            G->S[degree++] = env.n-offset;
            G->inS[env.n-offset] = degree;
        }
#endif        
    }
    G->degree = degree;
    
    return G;
}

digraph_t* create_complete_digraph()
{
    uint32_t u, v, idx;
    digraph_t *G = new_digraph();
    G->degree = env.n - 1;
    for (u = 0; u < env.n; u++) {
        for (v = u+1; v < env.n; v++) {
            if (u == v) continue;
            /* Add (u,v) edge */
            G->S[u*G->degree + v-1] = v;
            G->inS[u*env.n + v] = v-1;
            G->Nin[v*G->degree + u] = u;
            G->inNin[v*env.n + u] = u;
            /* Add (v,u) edge */
            G->S[v*G->degree + u] = u;
            G->inS[v*env.n + u] = u;
            G->Nin[u*G->degree + v-1] = v;
            G->inNin[u*env.n + v] = v-1;
        }
    }
    return G;
}

/**
 * Create a digraph with quasiminimal diameter [1]
 * 
 * Note: degree <= n/2 and degree >= 3
 * also, n <= degree^3 + degree, the diameter is quasiminimal
 * 
 * [1] T Soneoka, M Imase, Y Manabe: Design of a d-connected digraph 
 * with a minimum number of edges and a quasiminimal diameter: II, 1996
 */
digraph_t* create_sim_digraph(uint32_t degree, uint32_t pivot)
{
	digraph_t *G;
	line_label_t *line_label;
	uint32_t m, t, u, v, w, i, j, k, loop_count, Yoffset;
	uint32_t *prev_loop, cycle_start[2], *Nin_idx, *S_idx, *X;
    
    if ((2*degree > env.n) || (degree < 3)) {
        info("Warning: SIM digraph requires degree <= n/2 and degree >= 3\n");
        return NULL;
    }
	
	/* n = m*degree + t */
	m = env.n / degree;
	t = env.n % degree;
	
	if (pivot >= m) {
		pivot = m-1;
	}
	
	/* Create new digraph */
	G = new_digraph();
	
	/* Regular graph */
	G->degree = degree;
	
	for (u = 0; u < env.n; u++) {
		for (i = 0; i < G->degree; i++) {
			G->S[u*G->degree+i] = UINT32_MAX;
		}
	}
	
	//~ info("n=%d, d=%d, m=%d, t=%d\n", env.n,degree,m,t);
	
	/* Init previous self-loop array */
	loop_count = (degree - 1)/m + 1;
	prev_loop = (uint32_t*)env.data; 
	for (i = 0; i < loop_count; i++) {
		prev_loop[i] = UINT32_MAX;
	}
	
	/* Create line-label array */
	line_label = (line_label_t*)(prev_loop + loop_count);
	for (i = 0; i < m*degree; i++) {
		line_label[i].u = 0;
		line_label[i].v = 0;
	}
	 
	for (j = 0, u = 0; u < m; u++) {
		k = 0;
		for (i = 0; i < degree; i++) {
			line_label[j].u = u;
			v = (u*degree + i)%m;
			line_label[j].v = v;
			if (u == v) {
				/* Remove self-loop */
				if (prev_loop[k] == UINT32_MAX) {
					/* Start a new cycle */
					prev_loop[k] = j;
					if (k == loop_count - 1) {
						cycle_start[1] = u;
					}
					else {
						cycle_start[0] = u;
					}
				}
				else {
					/* Connect previous node in the cycle */
					line_label[prev_loop[k]].v = u;
					prev_loop[k] = j;
				}
				k++;
			}
			j++;
		}
	}
	for (i = 0; i < loop_count-1; i++) {
		line_label[prev_loop[i]].v = cycle_start[0];
	}
	line_label[prev_loop[loop_count-1]].v = cycle_start[1];
	
	//~ info("L(Gb*(%d, %d)): ", m, degree);
	//~ for (i = 0; i < m*degree; i++) {
		//~ info("(%d,%d) ", line_label[i].u, line_label[i].v);
	//~ }
	//~ info("\n");
	
	/* Initialize index array for reverse connection */
	Nin_idx = (uint32_t*)(line_label + m*degree);
	S_idx = Nin_idx + env.n;
	memset(Nin_idx, 0, env.n*sizeof(uint32_t));
	memset(S_idx, 0, env.n*sizeof(uint32_t));
	if (0 == t) goto linear_digraph;
	
	
	/* Get the set of vertexes corresponding to the edges incident to 
	 * the pivot in Gb*(m,degree) */
	X = S_idx + env.n; 
	memset(X, 0, degree*sizeof(uint32_t));
	j = 0;
	for (i = 0; i < m*degree; i++) {
		if (line_label[i].v == pivot) {
			X[j++] = i;
		}
	}
	
	/* Connect the last t vertexes with each other */
	for (i = m*degree; i < env.n; i++) {
		k = 0;
		for (j = m*degree; j < env.n; j++) {
			if (i == j) continue;
			G->S[i*degree + k] = j;
			G->inS[i*env.n + j] = ++k;
			G->Nin[j*degree + Nin_idx[j]] = i;
			G->inNin[j*env.n + i] = ++Nin_idx[j];
		}
	}
	
	/* Add remaining edges for the last t vertexes */
	Yoffset = pivot*degree;
	for (i = 0, w=m*degree; i < t; i++, w++) {
		k = t-1;
		/* Add edges for node m*degree+i */
		for (j = i; j <= i + degree-t; j++) {
			/* Y={(pivot,u)} line_label[pivot*degree:pivot*(degree+1)-1] */
			G->S[w*degree + k] = Yoffset + j;
			G->inS[w*env.n + Yoffset + j] = ++k;
			G->Nin[(Yoffset + j)*degree + Nin_idx[Yoffset + j]] = w;
			G->inNin[(Yoffset + j)*env.n + w] = ++Nin_idx[Yoffset + j];
			
			/* X={(u,0)} */
			G->Nin[w*degree + Nin_idx[w]] = X[j];
			G->inNin[w*env.n + X[j]] = ++Nin_idx[w];
			G->S[X[j]*degree + S_idx[X[j]]] = w;
			G->inS[X[j]*env.n + w] = ++S_idx[X[j]];
		}
	}
				
	//~ return G;
	
	/* Create edges for L(Gb*(m,degree)) */
	uint32_t starti, endi, xidx, skip;
	for (i = 0; i < m*degree; i++) {
		w = line_label[i].v*degree;
		for (j = w; j < w+degree; j++) {
			if (pivot == line_label[i].v) {
				skip = 0;
				/* j is a vertex in Y: check if edge part of Mi */
				for (xidx = 0; xidx < degree; xidx++) {
					if (X[xidx] == i) {
						break;
					}
				}
				/* xidx is the index of vertex i in the X set */
				starti = degree-t > xidx ? 0 : xidx - (degree-t);
				endi = xidx > t-1 ? t-1 : xidx;
				for (k = starti; k <= endi; k++) {
					if (j == w + k + xidx % (degree-t+1)) {
						skip = 1;
					}
				}
				if (skip) {
					continue;
				}
			}
			/* (i,j) is an edge */
			G->S[i*degree + S_idx[i]] = j;
			G->inS[i*env.n + j] = ++S_idx[i];
			G->Nin[j*degree + Nin_idx[j]] = i;
			G->inNin[j*env.n + i] = ++Nin_idx[j];
		}
	}
	
	return G;
	
linear_digraph:	
	/* Create edges for L(Gb*(m,degree)) */
	for (i = 0; i < m*degree; i++) {
		w = line_label[i].v*degree;
		for (j = w; j < w+degree; j++) {
			/* (i,j) is an edge */
			G->S[i*degree + S_idx[i]] = j;
			G->inS[i*env.n + j] = ++S_idx[i];
			G->Nin[j*degree + Nin_idx[j]] = i;
			G->inNin[j*env.n + i] = ++Nin_idx[j];
		}
	}
	
	return G;
}

/**
 * Create a copy of a digraph (both graphs need to be allocated)
 */
void copy_digraph(digraph_t *src_G, digraph_t *dst_G)
{
    memcpy(dst_G, src_G, sizeof(digraph_t) + src_G->data_size);
    dst_G->S = (uint32_t*)dst_G->data;
    if (dst_G->circulant) {
		dst_G->inS = dst_G->S + env.n;
		dst_G->freq = dst_G->inS + env.n;
		dst_G->improve = dst_G->freq + env.n;
	}
	else {
		uint32_t n_sq = env.n * env.n;
		dst_G->inS = dst_G->S + n_sq;
		dst_G->Nin = dst_G->inS + n_sq;
		dst_G->inNin = dst_G->Nin + n_sq;
	}
}

/**
 * Destroy digraph
 */
void destroy_digraph(digraph_t **G)
{
    if (NULL == *G) return;
    free(*G);
    *G = NULL;
}


/**
 * Set the fault tolerance
 */
void set_digraph_ft(digraph_t *G, uint32_t f)
{
	if (G) {
		G->attrs.f = f;
	}
}

uint32_t get_successor(digraph_t *G, uint32_t u, uint32_t idx)
{
    if (NULL == G) return UINT32_MAX;
    if (u >= env.n) return UINT32_MAX;
    if (idx >= G->degree) return UINT32_MAX;
    
    if (G->circulant) {
        return (u + G->S[idx])%env.n;
	}
	else {
        return G->S[u*G->degree + idx];
	}
}

uint32_t get_predecessor(digraph_t *G, uint32_t v, uint32_t idx)
{
    if (NULL == G) return UINT32_MAX;
    if (v >= env.n) return UINT32_MAX;
    if (idx >= G->degree) return UINT32_MAX;
    
    if (G->circulant) {
        return (v + env.n - G->S[idx])%env.n;
	}
	else {
        return G->Nin[v*G->degree + idx];
	}
}

uint32_t get_predecessor_idx(digraph_t *G, uint32_t v, uint32_t u)
{
    uint32_t idx;

    if (NULL == G) return UINT32_MAX;
    if (v >= env.n) return UINT32_MAX;
    if (u >= env.n) return UINT32_MAX;
    
    if (G->circulant) {
        for (idx = 0; idx < G->degree; idx++) {
            if ((u + G->S[idx]) % env.n == v) {
                return idx;
            }
        }
	}
	else {
        for (idx = 0; idx < G->degree; idx++) {
            if (u == G->Nin[v*G->degree + idx]) {
                return idx;
            }
        }
	}
    return UINT32_MAX;
}

/**
 * Generate a random regular digraph
 */
void rand_digraph(digraph_t *G, uint32_t degree)
{
	struct timeval tv;
	uint32_t *in_degrees = (uint32_t*)env.data;
	uint32_t *out_degrees = in_degrees + env.n;
	uint32_t src_count, dst_count, i, u, v, offset, retry_count;
	uint32_t nsq = env.n*env.n;
	int rand_src, rand_dst;
    G->degree = degree;
    
    /* Get a random pair */
    while (1) {
		/* Set seed */
		gettimeofday(&tv,NULL);
		srand48(tv.tv_sec*1e6+tv.tv_usec);
		for (i = 0; i < env.n; i++) {
			in_degrees[i] = degree;
			out_degrees[i] = degree;
		}
		memset(G->inS, 0, nsq*sizeof(uint32_t));
		memset(G->inNin, 0, nsq*sizeof(uint32_t));
		src_count = env.n*degree;
		dst_count = src_count;
		retry_count = 0;
		while (src_count) {
			rand_src = (int)(lrand48() % src_count + 1);
			rand_dst = (int)(lrand48() % dst_count + 1);
			for (i = 0; i < env.n; i++) {
				if (rand_src > 0) {
					rand_src -= out_degrees[i];
					if (rand_src <= 0) {
						u = i;
					}
				}
				if (rand_dst > 0) {
					rand_dst -= in_degrees[i];
					if (rand_dst <= 0) {
						v = i;
					}
				}
			}
			//~ info("u=%d, v=%d\n", u,v);
			if (u == v) {
				/* Loop */
				retry_count++;
				if (retry_count > 0.1 * env.n*degree) break;	
				continue;
			}
			//~ offset = v >= u ? v-u : v+env.n-u;
			if (G->inS[u*env.n + v]) {
				/* Multiple edge */
				retry_count++;
				if (retry_count > 0.1 * env.n*degree) break;	
				continue;
			}
			retry_count = 0;
			
			/* Add edge */
			G->S[u*degree + degree - out_degrees[u]] = v;
			out_degrees[u]--;
			src_count--;
			G->inS[u*env.n + v] = degree - out_degrees[u];
			
			G->Nin[v*degree + degree - in_degrees[v]] = u;
			in_degrees[v]--;
			dst_count--;
			G->inNin[v*env.n + u] = degree - in_degrees[v];
		}
		//~ info("\n");
		if (!src_count) break;
	}
}

/**
 * Generate a random circulant digraph
 */
void rand_circ_digraph(circ_digraph_t *G, uint32_t degree)
{  
    uint32_t i, src, count, offset;
    G->degree = degree;
    
    /* Set seed */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
	/* Generate random offsets */
	count = 0;
	memset(G->inS, 0, env.n*sizeof(uint32_t));
	/* Uncomment the following lines to include 1 all the times */
	//~ G->S[count] = 1;
	//~ G->inS[1] = ++count;
	while (count != G->degree) {
		offset = (uint32_t)(lrand48() % (env.n-1) + 1);
		if (G->inS[offset]) continue;
		/* found an offset */
		G->S[count] = offset;
		G->inS[offset] = ++count;
	}
}

/**
 * Generate next circulant digraph (exhaustive search)
 */
int next_circ_digraph(circ_digraph_t *G, uint32_t degree)
{
    int i, j;
    if (G->degree != degree) {
        /* First combination of offsets */
        G->degree = degree;
        for (i = 1; i <= degree; i++) {
            G->S[i-1] = i;
            G->inS[i] = i;
        }
        for (; i < env.n; i++)
            G->inS[i] = 0;
        return 1;
    }
    else {
        /* Find the greatest offset that can be incremented */
        for (i = degree-1; i >= 0; i--) {
            if (G->S[i] < env.n-1 - (degree-1-i))
                break;
        }
        if (i < 0) return 0;
        G->inS[G->S[i]] = 0;
        G->inS[++(G->S[i])] = i+1;
        /* Set all the subsequent offsets */
        for (j = i+1; j < degree; j++) {
            G->inS[G->S[j]] = 0;
            G->S[j] = G->S[j-1]+1;
            G->inS[G->S[j]] = j+1;
        }
        return 1;
    }
}

/**
 * Randomly replace an offset of a circulant digraph
 * @return #evaluations
 */
uint32_t mutate_circ_digraph_rand(circ_digraph_t* G)
{
    uint32_t idx, offset;
    if (G->degree == env.n - 1) return 0;
    
    /* Select random offset index */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    idx = (uint32_t)(lrand48() % G->degree);
    
    /* Randomly select replacement offset */
    while (1) {
        offset = (uint32_t)(lrand48() % (env.n-1) + 1);
        if (!G->inS[offset]) break;
    }
    /* Replace offset */
    G->inS[G->S[idx]] = 0;
    G->S[idx] = offset;
    G->inS[offset] = idx+1;
    
    return 0;
}

/**
 * Replace "the worst" offset of a circulant digraph 
 * with a randomly selected one
 * @return #evaluations
 */
uint32_t mutate_circ_digraph_greedy(circ_digraph_t* G)
{
    double *p_array;
    uint32_t idx, offset;
    double normalization = 0, p, q;
    if (G->degree == env.n - 1) return 0;
    
    p_array = (double*)env.data;
    
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
    /* Select an offset to replace using a distribution 
     * given by the usage frequency */
    for (idx = 0; idx < G->degree; idx++) {
        if (0 == G->freq[idx]) {
            goto replace;
        }
        p_array[idx] = 1./exp(0.1*G->freq[idx]);
        normalization += p_array[idx];
    }
    
    //~ print("prob: ");
    //~ for (idx = 0; idx < G->degree; idx++) {
        //~ print("%d(%lf) ", G->freq[idx],p_array[idx] / normalization);
    //~ }
    //~ print("\n");
    
    p = drand48();
    //~ print("rnd p: %lf\n", p);
    for (idx = 0; idx < G->degree; idx++) {
        q = p_array[idx] / normalization;
        if (p > q) p -= q;
        else break;
    }

replace: 
    /* Select replacement offset using a uniform distribution */
    while (1) {
        offset = (uint32_t)(lrand48() % (env.n-1) + 1);
        if (!G->inS[offset]) break;
    }
    /* Replace offset */
    G->inS[G->S[idx]] = 0;
    G->S[idx] = offset;
    G->inS[offset] = idx+1;
    
    return 0;
}

/**
 * Mutate a circulant digraph by
 * adding an offset and then removing one, in a greedy fashion
 * @return #evaluations
 */
uint32_t mutate_circ_digraph_2phase(circ_digraph_t* G)
{   
	uint32_t ssp_count;
    uint32_t depth = G->attrs.DfU;
    uint32_t lpc = G->attrs.lpc;
    
    /* Add offset */
    if (1 == add_offset_greedy(G)) return 0;
    
    /* Compute new depth */
    ssp_count = digraph_fault_diameter(G, UINT32_MAX, 0);
    
    /* Remove offset */
    rm_offset_greedy(G, 1);
    
    return ssp_count;
} 

/** 
 * Add a random offset to a circulant digraph
 */
int add_offset_rand(circ_digraph_t* G)
{
    uint32_t offset;
    if (G->degree == env.n - 1) return 1;
   
    /* Randomly select an offset */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    while (1) {
        offset = (uint32_t)(lrand48() % (env.n-1) + 1);
        if (!G->inS[offset]) break;
    }
    
    /* Add offset */
    G->S[G->degree] = offset;
    G->degree++;
    G->inS[offset] = G->degree;
    
    return 0;
}

/**
 * Add an offset according to a distribution given by 
 * the maximum minimum improvement
 */
int add_offset_greedy(circ_digraph_t* G)
{
    double *p_array;
    uint32_t offset;
    double normalization = 0, p, q;
    if (G->degree == env.n - 1) return 1;
    
    p_array = (double*)env.data;
      
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
    /* Select an offset to add using a distribution 
     * given by the minimum improvement */
    for (offset = 1; offset < env.n; offset++) {
        p_array[offset] = G->improve[offset];
        p_array[offset] *= p_array[offset];
        //~ p_array[offset] *= p_array[offset];
        normalization += p_array[offset];
    }
    //~ print("prob: ");
    //~ for (offset = 1; offset < env.n; offset++) {
        //~ print("%d(%lf) ", offset,p_array[offset] / normalization);
    //~ }
    //~ print("\n");
    p = drand48();
    for (offset = 1; offset < env.n; offset++) {
        q = p_array[offset] / normalization;
        if (p > q) p -= q;
        else break;
    }
    
    /* Add offset */
    G->S[G->degree] = offset;
    G->inS[offset] = ++G->degree;
    
    return 0;
}

/**
 * TODO
 * Add an offset according to a distribution given by 
 * the minimum overall improvement
 */
 

/**
 * Remove a random offset
 * @param not_last indicates if the last offset can be removed 
 */
int rm_offset_rand(circ_digraph_t* G, int not_last)
{
    uint32_t idx, offset;
    
    /* Select random offset to remove */
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    if (not_last) {
        idx = (uint32_t)(lrand48() % (G->degree-1));
    } else {
        idx = (uint32_t)(lrand48() % G->degree);
    }
    
    /* Remove offset */
    G->degree--;
    G->inS[G->S[idx]] = 0;
    if (idx < G->degree) {
        G->S[idx] = G->S[G->degree];
        G->inS[G->S[idx]] = idx+1;
    }
    
    return 0;
}

/**
 * Remove an offset according to a distribution given by 
 * the usage frequency
 * @param not_last indicates if the last offset can be removed 
 */
int rm_offset_greedy(circ_digraph_t* G, int not_last)
{
    double *p_array;
    uint32_t idx, offset, m;
    double normalization = 0, p, q;
    
    p_array = (double*)env.data;
    
    struct timeval tv;
    gettimeofday(&tv,NULL);
    srand48(tv.tv_sec*1e6+tv.tv_usec);
    
    /* Select an offset to replace using a distribution 
     * given by the usage frequency */
    if (not_last) m = G->degree - 1;
    else m = G->degree;
    for (idx = 0; idx < m; idx++) {
        if (0 == G->freq[idx]) {
            goto remove;
        }
        p_array[idx] = 1./G->freq[idx];
        p_array[idx] *= p_array[idx];
        //~ p_array[idx] *= p_array[idx];
        normalization += p_array[idx];
    }
    
    p = drand48();
    for (idx = 0; idx < m; idx++) {
        q = p_array[idx] / normalization;
        if (p > q) p -= q;
        else break;
    }

remove:
    /* Remove offset */
    G->degree--;
    G->inS[G->S[idx]] = 0;
    if (idx < G->degree) {
        G->S[idx] = G->S[G->degree];
        G->inS[G->S[idx]] = idx+1;
    }
    
    return 0;
}

/**
 * Compute the connectivity of a regular digraph
 */
void digraph_connectivity(digraph_t* G)
{
	if (G->circulant) {
		circ_digraph_connectivity(G);
	}
	else {
		uint32_t src, dst, *inS;
		G->attrs.k = env.n - 1;
		for (src = 0; src < env.n; src++) {
			inS = G->inS + src*env.n;
			for (dst = 0; dst < env.n; dst++) {
				if (src == dst) continue;
				if (inS[dst]) continue;
				//~ info("da_cherkassky %d->%d\n", src, dst);
				da_cherkassky(G, src, dst);
			}
			break;
		}
	}
}

/**
 * Compute the diameter of a regular digraph
 */
void digraph_diameter(digraph_t* G)
{
	uint32_t root, sp;
	G->attrs.D = 1;
	if (G->circulant) {
		G->attrs.D = largest_shorthest_path(G, 0);
	}
	else {
		for (root = 0; root < env.n; root++) {
			sp = largest_shorthest_path(G, root);
			if (sp > G->attrs.D) {
				G->attrs.D = sp;
			}
		}
	}
}

/**
 * Compute lower bound of the diameter (Moore's bound)
 */
uint32_t min_diameter(uint32_t n, uint32_t degree)
{
	return ceil(log(n*(degree-1) + degree)/log(degree))-1;
}

/**
 * Compute the fault diameter (bounds) of a regular digraph
 */
uint32_t digraph_fault_diameter( digraph_t* G, 
                                 uint32_t ub_Dfu, 
                                 uint32_t ub_lpc )
{
	uint32_t s = 0, t, i;
    uint32_t ssp_count = 0, *inS;
    
    G->attrs.DfU = 1;
    G->attrs.DfL = 1;
    
    if (G->circulant) {
		memset(G->freq, 0, G->degree * sizeof(uint32_t));
		for (t = 1; t < env.n; t++) {
			if (G->inS[t]) continue;
			ssp(G,s,t);
			//~ info("ssp %d->%d: %d %d\n", s, t, G->attrs.DfU, G->attrs.lpc);
			ssp_count++;
			if ( (G->attrs.DfU > ub_Dfu) ||
					((G->attrs.DfU == ub_Dfu) &&
					(G->attrs.lpc > ub_lpc)) )
			{
				/* Bounded evaluation */
				break;
			}
		}
	}
	else {
		for (s = 0; s < env.n; s++) {
			inS = G->inS + s*env.n;
			for (t = 0; t < env.n; t++) {
				if (s == t) continue;
				if (inS[t]) continue;
				//~ info("ssp %d->%d\n", s, t);
				ssp(G,s,t);
				ssp_count++;
				if ( (G->attrs.DfU > ub_Dfu) ||
						((G->attrs.DfU == ub_Dfu) &&
						(G->attrs.lpc > ub_lpc)) )
				{
					/* Bounded evaluation */
					break;
				}
			}
		}
	}
	
    return ssp_count;
}

void print_digraph(digraph_t* G)
{
    uint32_t i, src, *S, *Nin;
    if (G->circulant) {
		info("G=(%"PRIu32",[ ", env.n);
		for (i = 0; i < G->degree; i++) {
			info("%"PRIu32" ", G->S[i]);
		}
		info("])\n");
	}
	else {
		for (src = 0; src < env.n; src++) {
			S = G->S + src*G->degree;
			info("v%"PRIu32": ", src);
			for (i = 0; i < G->degree; i++) {
				if (UINT32_MAX == S[i]) info("x ");
				else info("%"PRIu32" ", S[i]);
			}
			Nin = G->Nin + src*G->degree;
			info("   ");
			for (i = 0; i < G->degree; i++) {
				info("%"PRIu32" ", Nin[i]);
			}
			info("\n");
		}
		info("\n");
	}
}

void digraph2dot(digraph_t* G, char *dot_file)
{
	FILE *dot;
	uint32_t i,u;
	char cmd[256];
	char *tmp_file = "tmp.gv";
	
	/* Open data file */
	if (NULL == dot_file) {
		dot_file = "digraph";
	}
    if (strcmp(dot_file, "") == 0) {
        dot_file = "digraph";
    }
    sprintf(cmd, "%s.gv", dot_file);
    dot = fopen(cmd, "w+");
    if (NULL == dot) {
        info("Error: Cannot open dot file\n");
        return;
    }
    fprintf(dot, "digraph SIM {\n");
    //~ fprintf(dot, "   node [color=black,fillcolor=\"#C0DDD3\",shape=box,style=\"filled,rounded\"]");
    //~ fprintf(dot, "   node [color=black,fillcolor=\"#C0DDD3\",shape=ellipse,style=\"filled\"]");
    fprintf(dot, "   node [color=black,fillcolor=\"#C0DDD3\",shape=ellipse,style=\"filled\"]");
    
    
    for (u = 0; u < env.n; u++) {
		fprintf(dot, "   %d [label=<<FONT POINT-SIZE=\"30\">p<SUB>%d</SUB></FONT>>]\n", u, u);
	}
    fprintf(dot, "   edge [color=white]\n");
    fprintf(dot, "   0");
    for (u = 1; u < env.n; u++) {
		fprintf(dot, " -> %"PRIu32, u);
	}
	fprintf(dot, " -> 0\n}\n");
	fclose(dot);
		
	sprintf(cmd, "circo %s.gv > %s", dot_file, tmp_file);
	system(cmd);
	//~ sprintf(cmd, "cat < %s > %s.gv", tmp_file, dot_file);
	sprintf(cmd, "head -n -1 < %s > %s.gv", tmp_file, dot_file);
	system(cmd);
	remove(tmp_file);
		
	sprintf(cmd, "%s.gv", dot_file);
    dot = fopen(cmd, "a");
    if (NULL == dot) {
        info("Error: Cannot open dot file\n");
        return;
    }
    fprintf(dot, "edge [style=bold, color=black]\n");
	if (G->circulant) {
		for (u = 0; u < env.n; u++) {
			fprintf(dot, "   %"PRIu32" -> {%"PRIu32, u, (u+G->S[0])%env.n);
			for (i = 1; i < G->degree; i++) {
				fprintf(dot, " %"PRIu32, (u+G->S[i])%env.n);
			}
			fprintf(dot, "}\n");
		}
	}
	else {
		for (u = 0; u < env.n; u++) {
			//~ if (0 != G->S[u*G->degree]) continue;
			if (UINT32_MAX == G->S[u*G->degree]) continue;
			fprintf(dot, "   %"PRIu32" -> {%"PRIu32, u, G->S[u*G->degree]);
			for (i = 1; i < G->degree; i++) {
				if (UINT32_MAX == G->S[u*G->degree+i]) break;
				fprintf(dot, " %"PRIu32, G->S[u*G->degree + i]);
			}
			fprintf(dot, "}\n");
		}
	}
	fprintf(dot, "}\n");
    fclose(dot);

	sprintf(cmd, "neato -n %s.gv -Tpng > %s.png", dot_file, dot_file);
	system(cmd);
    //~ sprintf(cmd, "%s.gv", dot_file);
    //~ remove(cmd);
}

void graph2dot(digraph_t* G, char *dot_file)
{
	FILE *dot;
	uint32_t i,u, v;
	char cmd[256];
	char *tmp_file = "tmp.gv";
	
	/* Open data file */
	if (NULL == dot_file) {
		dot_file = "digraph";
	}
    if (strcmp(dot_file, "") == 0) {
        dot_file = "digraph";
    }
    sprintf(cmd, "%s.gv", dot_file);
    dot = fopen(cmd, "w+");
    if (NULL == dot) {
        info("Error: Cannot open dot file\n");
        return;
    }
    fprintf(dot, "graph BG {\n");
    fprintf(dot, "   node [color=black,fillcolor=\"#C0DDD3\",shape=ellipse,style=\"filled\"]");
    
    for (u = 0; u < env.n; u++) {
		fprintf(dot, "   %d [label=<<FONT POINT-SIZE=\"40\">p<SUB>%d</SUB></FONT>>]\n", u, u+1);
	}
    fprintf(dot, "   edge [color=white]\n");
    fprintf(dot, "   0");
    for (u = 1; u < env.n; u++) {
		fprintf(dot, " -- %"PRIu32, u);
	}
	fprintf(dot, " -- 0\n}\n");
	fclose(dot);
		
	sprintf(cmd, "circo %s.gv > %s", dot_file, tmp_file);
	system(cmd);
    
	//~ sprintf(cmd, "cat < %s > %s.gv", tmp_file, dot_file);
	sprintf(cmd, "head -n -1 < %s > %s.gv", tmp_file, dot_file);
	system(cmd);
	remove(tmp_file);
		
	sprintf(cmd, "%s.gv", dot_file);
    dot = fopen(cmd, "a");
    if (NULL == dot) {
        info("Error: Cannot open dot file\n");
        return;
    }
    fprintf(dot, "edge [style=bold, color=black]\n");
    //~ fprintf(dot, "edge [style=bold, color=white]\n");
#if 1   
	if (G->circulant) {
		for (u = 0; u < env.n; u++) {
            for (i = 0; i < G->degree; i++) {
                v = (u+G->S[i])%env.n;
                if (v < u) continue;
                break;
            }
            if (i == G->degree) continue;
			fprintf(dot, "   %"PRIu32" -- {%"PRIu32, 
                                        u, (u+G->S[i++])%env.n);
			for (; i < G->degree; i++) {
                v = (u+G->S[i])%env.n;
                if (v < u) continue;
				fprintf(dot, " %"PRIu32, (u+G->S[i])%env.n);
			}
			fprintf(dot, "}\n");
		}
	}
	else {
		for (u = 0; u < env.n; u++) {
			//~ if (0 != G->S[u*G->degree]) continue;
			if (UINT32_MAX == G->S[u*G->degree]) continue;
            for (i = 0; i < G->degree; i++) {
                v = G->S[u*G->degree];
                if (v < u) continue;
                break;
            }
            if (i == G->degree) continue;
			fprintf(dot, "   %"PRIu32" -- {%"PRIu32, 
                                    u, G->S[u*G->degree + i++]);
			for (; i < G->degree; i++) {
				if (UINT32_MAX == G->S[u*G->degree+i]) break;
				fprintf(dot, " %"PRIu32, G->S[u*G->degree + i]);
			}
			fprintf(dot, "}\n");
		}
	}
#else
   //~ fprintf(dot, "   0 -- {1 11 2 10 4 8}\n");
   fprintf(dot, "   0 -- {11 10}\n");
   fprintf(dot, "   1 -- {2 3 11 5 9}\n");
   //~ fprintf(dot, "   2 -- {3 4 6 10}\n");
   fprintf(dot, "   2 -- {4 6 10}\n");
   fprintf(dot, "   3 -- {4 5 7 11}\n");
   //~ fprintf(dot, "   4 -- {5 6 8}\n");
   fprintf(dot, "   4 -- {8}\n");
   fprintf(dot, "   5 -- {6 7 9}\n");
   //~ fprintf(dot, "   6 -- {7 8 10}\n");
   fprintf(dot, "   6 -- {8 10}\n");
   fprintf(dot, "   7 -- {8 9 11}\n");
   //~ fprintf(dot, "   8 -- {9 10}\n");
   fprintf(dot, "   9 -- {10 11}\n");
   //~ fprintf(dot, "   10 -- {11}\n");
   
    fprintf(dot, "   subgraph Rel1 {\n");
    fprintf(dot, "   edge [dir=forward, color=red, penwidth = 5, arrowsize=2]\n");
    fprintf(dot, "   0 -- {1, 2, 4, 8}\n");
    fprintf(dot, "   2 -- {3}\n");
    fprintf(dot, "   4 -- {5, 6}\n");
    fprintf(dot, "   6 -- {7}\n");
    fprintf(dot, "   8 -- {9, 10}\n");
    fprintf(dot, "   10 -- {11}\n");
    fprintf(dot, "}\n");
#endif    
	fprintf(dot, "}\n");
    fclose(dot);

	sprintf(cmd, "neato -n %s.gv -Tpng > %s.png", dot_file, dot_file);
	system(cmd);
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

/**
 * Compute the connectivity of a circulant digraph according 
 * to Erik A. van Doorn:"Connectivity of a circulant digraph", 1986.
 */
static void 
circ_digraph_connectivity(circ_digraph_t* G)
{
    uint32_t r = 1, l, inv_r, i;
    uint32_t count, cut_size;
    uint8_t *buffer = (uint8_t*)env.data;
    
    G->attrs.k = env.n-1;
    
    if (G->degree == env.n-1)
        return;
    
    while(r < sqrt(env.n)) {
        if (0 == env.n % r) {
            /* compute |M(r,S)| */
            count = 0;
            memset(buffer, 0, env.n*sizeof(uint8_t));
            for (i = 0; i < G->degree; i++) {
                l = G->S[i] % r;
                if ((l > 0) && (!buffer[l]))
                {
                    count++;
                    buffer[l] = 1;
                }
            }
            //~ print("|M(%d, S)|=%d\n", r, count);
            if (count < r - 1) {
                cut_size = inv_r * count;
                //~ print("   cut_size=%d\n", cut_size);
                G->attrs.k = G->attrs.k < cut_size ? G->attrs.k : cut_size;
            }
            /* compute |M(n/r,S)| */
            inv_r = env.n / r;
            count = 0;
            memset(buffer, 0, env.n*sizeof(uint8_t));
            for (i = 0; i < G->degree; i++) {
                l = G->S[i] % inv_r;
                if ((l > 0) && (!buffer[l]))
                {
                    count++;
                    buffer[l] = 1;
                }
            }
            //~ print("|M(%d, S)|=%d\n", inv_r, count);
            if (count < inv_r - 1) {
                cut_size = r * count;
                //~ print("   cut_size=%d\n", cut_size);
                G->attrs.k = G->attrs.k < cut_size ? G->attrs.k : cut_size;
            }
        }
        r++;
    }
    if (r*r == env.n) {
        /* compute |M(r,S)| */
        count = 0;
        memset(buffer, 0, env.n*sizeof(uint8_t));
        for (i = 0; i < G->degree; i++) {
            l = G->S[i] % r;
            if ((l > 0) && (!buffer[l]))
            {
                count++;
                buffer[l] = 1;
            }
        }
        //~ print("|M(%d, S)|=%d\n", r, count);
        if (count < r - 1) {
            cut_size = r * count;
            //~ print("   cut_size=%d\n", cut_size);
            G->attrs.k = G->attrs.k < cut_size ? G->attrs.k : cut_size;
        }
    }
}

/**
 * Round up to next higher power of 2
 */
static inline uint32_t
pow2roundup (uint32_t x)
{
    if (x == 0)
        return 0;
    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x+1;
}

/**
 * Round up log2
 */
static inline uint32_t
log2roundup (uint32_t x)
{
    uint32_t log = 0;
    x = pow2roundup(x);
    while (x) {
        x >>= 1;
        log++;
    }
    return log-1;
}

#endif
