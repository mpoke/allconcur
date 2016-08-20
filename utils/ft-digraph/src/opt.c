/**                                                                                                      
 * Fault tolerant circulant digraphs
 * 
 * Optimization methods
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <math.h>
#include <signal.h>
#include <limits.h>
#include <string.h>

#include <opt.h>
#include <digraph.h>
#include <timer.h>
#include <debug.h>
#include <fib.h>


/* ================================================================== */
/* Type definitions */
#if 1

/* Optimization solution */
struct opt_sol_t {
	obj_func_t obj_func;	// objective function
	circ_digraph_t *G;		// pointer to a circulant digraph
};
typedef struct opt_sol_t opt_sol_t;

/* Optimization environment  */
struct opt_env_t {
	uint32_t sol_count;
	opt_sol_t *sol_array;
	circ_digraph_t *G[2];
    uint32_t data_size;
    void *data;
};
typedef struct opt_env_t opt_env_t;

#endif

/* ================================================================== */
/* Global variables */
#if 1

int set_opt_env;
opt_sol_t best_sol;
opt_env_t opt_env; 
extern unsigned long long g_timerfreq;
extern int timer;
static const int opt_debug =  0;
static const int opt_stats =  1;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
init_opt_env();

static int 
cmpfunc_solution(const void *a, const void *b);
static void 
opt_statistics();

static int 
random_search( uint32_t n,
			   uint32_t degree, 
               uint32_t f,
               int debug,
               int stats );
static void 
hill_climbing( uint32_t (*mutate)(circ_digraph_t*),
			   uint32_t n,
			   uint32_t degree, 
               uint32_t f,
               int *avail_sp_count,
               int debug,
               int stats );

#endif

/* ================================================================== */
/* Global functions */
#if 1



void optimize( uint32_t n, 
               uint32_t degree, 
               uint32_t f, 
               obj_func_t ub, 
               int opt_type )
{
	HRT_TIMESTAMP_T t1, t2;
	uint64_t ticks;
	double elapsed_time;
	uint32_t i, j;
	int ssp_count;
	
	if (!set_opt_env) {
		init_opt_env();
	}
	
	switch (opt_type) {
		case OPT_EXAUST:
			break;
		case OPT_RAND:
		{
			for (i = 0; i < mc_repeat; i++) {
				opt_env.sol_count = 0;
				best_sol.obj_func.D = ub.D;
				best_sol.obj_func.DfU = ub.DfU;
				best_sol.obj_func.lpc = ub.lpc;
				info("Random search: ");
				if (timer) HRT_GET_TIMESTAMP(t1);
				ssp_count = random_search(n, degree, f, opt_debug, opt_stats);
				if (0 == opt_env.sol_count) {
					info("No solution!\n");
					continue;
				}
				info("G*=(%"PRIu32",[%"PRIu32, 
										env.n, best_sol.G->S[0]);
				for (j = 1; j < best_sol.G->degree; j++) {
					info(",%"PRIu32, best_sol.G->S[j]);
				}
				info("])\n");
				digraph_diameter(best_sol.G);
				info("   -> D=%d (Dmin=%d)\n", best_sol.G->attrs.D, 
							min_diameter(env.n, best_sol.G->degree));	
				info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
							best_sol.G->attrs.DfL, best_sol.G->attrs.DfU, 
							best_sol.G->attrs.lpc);
				info("   -> SSP calls: %"PRIu32"\n", ssp_count);
				
				if (opt_stats) {
					opt_statistics();
				}
				if (timer) {
					HRT_GET_TIMESTAMP(t2);
					HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
					elapsed_time = HRT_GET_SEC(ticks);
					info("...done (%lf s)\n", elapsed_time);
				}
			}
			break;
		}
		case OPT_HILL:
		{
			ssp_count = INT_MAX;
			best_sol.obj_func.D = ub.D;
			best_sol.obj_func.DfU = ub.DfU;
			best_sol.obj_func.lpc = ub.lpc;
			for (i = 0; i < mc_repeat; i++) {
				opt_env.sol_count = 0;
				info("Hill climber: ");
				if (timer) HRT_GET_TIMESTAMP(t1);
				hill_climbing(mutate_circ_digraph_2phase, n, degree, f, 
							&ssp_count, opt_debug, opt_stats);
				if (0 == opt_env.sol_count) {
					info("No solution!\n");
					continue;
				}
				info("G*=(%"PRIu32",[%"PRIu32, 
								env.n, best_sol.G->S[0]);
				for (j = 1; j < best_sol.G->degree; j++) {
					info(",%"PRIu32, best_sol.G->S[j]);
				}
				info("])\n");
				digraph_diameter(best_sol.G);
				info("   -> D=%d (Dmin=%d)\n", best_sol.G->attrs.D, 
							min_diameter(env.n, best_sol.G->degree));	
				info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
							best_sol.G->attrs.DfL, best_sol.G->attrs.DfU, 
							best_sol.G->attrs.lpc);
				if (opt_stats) {
					opt_statistics();
				}
				if (timer) {
					HRT_GET_TIMESTAMP(t2);
					HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
					elapsed_time = HRT_GET_SEC(ticks);
					info("...done (%lf s)\n", elapsed_time);
				}
			}
			break;
		}
		case OPT_CMP_RAND_HILL:
		{
			opt_env.sol_count = 0;
			best_sol.obj_func.D = ub.D;
			best_sol.obj_func.DfU = ub.DfU;
			best_sol.obj_func.lpc = ub.lpc;
			info("Random search: ");
			if (timer) HRT_GET_TIMESTAMP(t1);
			ssp_count = random_search(n, degree, f, opt_debug, opt_stats);
			if (0 == opt_env.sol_count) {
				info("No solution!\n");
			}
			else {
				info("G*=(%"PRIu32",[%"PRIu32, 
										env.n, best_sol.G->S[0]);
				for (j = 1; j < best_sol.G->degree; j++) {
					info(",%"PRIu32, best_sol.G->S[j]);
				}
				info("])\n");
				digraph_diameter(best_sol.G);
				info("   -> D=%d (Dmin=%d)\n", best_sol.G->attrs.D, 
							min_diameter(env.n, best_sol.G->degree));	
				info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
							best_sol.G->attrs.DfL, best_sol.G->attrs.DfU, 
							best_sol.G->attrs.lpc);
				info("   -> SSP calls: %"PRIu32"\n", ssp_count);
				
				if (opt_stats) {
					opt_statistics();
				}
			}
			if (timer) {
				HRT_GET_TIMESTAMP(t2);
				HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
				elapsed_time = HRT_GET_SEC(ticks);
				info("...done (%lf s)\n", elapsed_time);
			}
			
			opt_env.sol_count = 0;
			best_sol.obj_func.D = ub.D;
			best_sol.obj_func.DfU = ub.DfU;
			best_sol.obj_func.lpc = ub.lpc;
			info("Hill climber: ");
			if (timer) HRT_GET_TIMESTAMP(t1);
			while (ssp_count > 0) {
				/* Restart hill climbing */
				hill_climbing(mutate_circ_digraph_2phase, n, degree, f, 
						&ssp_count, opt_debug, opt_stats);
			}
			if (0 == opt_env.sol_count) {
				info("No solution!\n");
				break;
			}
			info("G*=(%"PRIu32",[%"PRIu32, 
									env.n, best_sol.G->S[0]);
			for (j = 1; j < best_sol.G->degree; j++) {
				info(",%"PRIu32, best_sol.G->S[j]);
			}
			info("])\n");
			digraph_diameter(best_sol.G);
			info("   -> D=%d (Dmin=%d)\n", best_sol.G->attrs.D, 
						min_diameter(env.n, best_sol.G->degree));	
			info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
						best_sol.G->attrs.DfL, best_sol.G->attrs.DfU, 
						best_sol.G->attrs.lpc);
			
			if (opt_stats) {
				opt_statistics();
			}
			if (timer) {
				HRT_GET_TIMESTAMP(t2);
				HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
				elapsed_time = HRT_GET_SEC(ticks);
				info("...done (%lf s)\n", elapsed_time);
			}
			break;
		}
		default: 
			info("Error: Unknown optimization type\n");
	}
	
	
}

void free_opt_env()
{
	if (best_sol.G) {
		destroy_digraph(&(best_sol.G));
		best_sol.G = NULL;
	}
	if (opt_env.G[0]) {
		destroy_digraph(&(opt_env.G[0]));
		opt_env.G[0] = NULL;
	}
	if (opt_env.G[1]) {
		destroy_digraph(&(opt_env.G[1]));
		opt_env.G[1] = NULL;
	}
    if (opt_env.data) {
		free(opt_env.data);
		opt_env.data = NULL;
	}
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

void init_opt_env()
{
    opt_env.data_size = sample_count*sizeof(opt_sol_t);
    opt_env.data = malloc(opt_env.data_size);
    
	opt_env.sol_array = (opt_sol_t*)opt_env.data;
	opt_env.G[0] = new_circ_digraph();
    opt_env.G[1] = new_circ_digraph();
    best_sol.G = new_circ_digraph();
    
    set_opt_env = 1;
}

/**
 * Compare opt_sol_t structures
 */
static int 
cmpfunc_solution(const void *a, const void *b)
{
    if ( ((opt_sol_t*)a)->obj_func.DfU > ((opt_sol_t*)b)->obj_func.DfU ) 
        return 1;
    if ( ((opt_sol_t*)a)->obj_func.DfU == ((opt_sol_t*)b)->obj_func.DfU ) {
        if ( ((opt_sol_t*)a)->obj_func.lpc > ((opt_sol_t*)b)->obj_func.lpc ) 
            return 1;
        if ( ((opt_sol_t*)a)->obj_func.lpc < ((opt_sol_t*)b)->obj_func.lpc ) 
            return -1;
    }
    return 0;
}

static void 
opt_statistics()
{
	int j;
	opt_sol_t *sa = opt_env.sol_array;
	uint32_t best_count, sol_count = opt_env.sol_count;
	
	/* How many solutions before the best found */
	for (j = 0; j < sol_count; j++) {
		if ( (sa[j].obj_func.DfU == best_sol.obj_func.DfU) && 
			 (sa[j].obj_func.lpc == best_sol.obj_func.lpc) )
			break;
	}
	info("   Found best solution  after %"PRIu32" iterations\n", j+1);
	
	/* Sort solution array */
	qsort(sa, sol_count, sizeof(opt_sol_t), cmpfunc_solution);
	
	/* Check best solution frequency */
	best_count = 0;
	for (j = 0; j < sol_count; j++) {
		if ( (sa[j].obj_func.DfU == best_sol.obj_func.DfU) && 
			 (sa[j].obj_func.lpc == best_sol.obj_func.lpc) ) 
			 break;
	}
	for (; j < sol_count; j++) {
		if ( (sa[j].obj_func.DfU != best_sol.obj_func.DfU) ||
			 (sa[j].obj_func.lpc != best_sol.obj_func.lpc) ) 
			break;
		best_count++;
	}
	info("   Freq. best       %"PRIu32"/%"PRIu32" (%lf%%)\n", 
		best_count, sol_count, 100.*best_count/sol_count);
		
	/* Various statistics */
	int first_quartile = (int)ceil(sol_count * 0.25) - 1;
	int second_quartile = (int)ceil(sol_count * 0.5) - 1;
	int third_quartile = (int)ceil(sol_count * 0.75) - 1;
	info("   %"PRIu32"(#%"PRIu32") | %"PRIu32"(#%"PRIu32
		") - %"PRIu32"(#%"PRIu32") - %"PRIu32"(#%"PRIu32
		") | %"PRIu32"(#%"PRIu32")\n", 
		sa[0].obj_func.DfU, sa[0].obj_func.lpc, 
		sa[first_quartile].obj_func.DfU, sa[first_quartile].obj_func.lpc,
		sa[second_quartile].obj_func.DfU, sa[second_quartile].obj_func.lpc,
		sa[third_quartile].obj_func.DfU, sa[third_quartile].obj_func.lpc,
		sa[sol_count-1].obj_func.DfU, sa[sol_count-1].obj_func.lpc);
}

/**
 * Random search 
 * @return #ssp calls
 */
static int 
random_search( uint32_t n,
			   uint32_t degree, 
               uint32_t f,
               int debug,
               int stats )
{
    uint32_t i, j, evals = 0;
    int ssp_count, total_ssp_count = 0;
    
    circ_digraph_t *G = opt_env.G[0];
    
    if (debug) {
        info("\n# Random search n=%d, degree=%d, f=%d (%d samples) #\n", 
            n, degree, f, sample_count);
	}
    
	/* Set circulant digraph's fault tolerance */
	set_digraph_ft(G, f);
    
    while (evals < sample_count) {
        /* Generate random solution */
        rand_circ_digraph(G, degree);
        
        /* Compute connectivity */
        digraph_connectivity(G);
        if (G->attrs.k <= f) {
            //~ if (debug) {
                //~ info("   G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
                //~ for (j = 1; j < G->degree; j++) {
                    //~ info(",%"PRIu32, G->S[j]);
                //~ }
                //~ info("]): infeasible k=%"PRIu32"\n", G->attrs.k);
            //~ }
            continue;
        }
        
        /* Compute diameter */
        digraph_diameter(G);

        /* Compute fault diameter */
        ssp_count = digraph_fault_diameter(G, best_sol.obj_func.DfU, 
										best_sol.obj_func.lpc);
		total_ssp_count += ssp_count;
        evals++;
        if (ssp_count < n-degree-1) {
			/* The evaluation was interrupted by the upper bound */
            continue;
        }
        if (stats) {
			opt_env.sol_array[opt_env.sol_count].obj_func.DfU = G->attrs.DfU;
			opt_env.sol_array[opt_env.sol_count].obj_func.lpc = G->attrs.lpc;
		}
		opt_env.sol_count++;
        
        if (debug) {
            info("   G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
            for (j = 1; j < G->degree; j++) {
                info(",%"PRIu32, G->S[j]);
            }
            info("]): DfL=%"PRIu32";DfU=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
                     G->attrs.DfL, G->attrs.DfU, G->attrs.lpc, G->attrs.k);
        }
        
        //~ if (G->attrs.DfU <= best_sol.obj_func.DfU) {
			//~ info("   G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
            //~ for (j = 1; j < G->degree; j++) {
                //~ info(",%"PRIu32, G->S[j]);
            //~ }
            //~ info("])\n");
            //~ info("   D=%"PRIu32"\n", G->attrs.D);
            //~ info("   DfL=%"PRIu32";DfU=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
                     //~ G->attrs.DfL, G->attrs.DfU, G->attrs.lpc, G->attrs.k);
		//~ }
		//~ else 
		if (G->attrs.D <= best_sol.obj_func.D) {
			info("   G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
            for (j = 1; j < G->degree; j++) {
                info(",%"PRIu32, G->S[j]);
            }
            info("])\n");
            info("   D=%"PRIu32"\n", G->attrs.D);
            info("   DfL=%"PRIu32";DfU=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
                     G->attrs.DfL, G->attrs.DfU, G->attrs.lpc, G->attrs.k);
		}
        
        if ( (G->attrs.DfU < best_sol.obj_func.DfU) ||
             ((G->attrs.DfU == best_sol.obj_func.DfU) && 
             (G->attrs.lpc <  best_sol.obj_func.lpc)) )
        {
            /* Better solution; keep it */
            best_sol.obj_func.DfU = G->attrs.DfU;
            best_sol.obj_func.lpc = G->attrs.lpc;
            best_sol.obj_func.DfL = G->attrs.DfL;          
            copy_digraph(G, best_sol.G);
        }    
    }
    
    return total_ssp_count;
}

/**
 * Hill climbing 
 * @param mutate mutation operator
 * @return #ssp calls 
 */
static void 
hill_climbing( uint32_t (*mutate)(circ_digraph_t*),
			   uint32_t n,
			   uint32_t degree, 
               uint32_t f,
               int *avail_ssp_count,
               int debug,
               int stats )
{
    circ_digraph_t *G = NULL;
    uint32_t j, prev, same_sol_count, evals = 0;
    uint32_t ssp_count;
    
    //~ if (debug) {
        //~ info("\n# Hill climbing n=%d, degree=%d, f=%d (%d samples) #\n", 
            //~ n, degree, f, sample_count);
	//~ }
		
    /* Set circulant digraph's fault tolerance */
    set_digraph_ft(opt_env.G[0],f);
    set_digraph_ft(opt_env.G[1],f);    

	/* Start a new round: 
	 * generate random (feasible) initial solution 
	 * TODO: Tabu Search */ 
	G = opt_env.G[0];
	while (1) { // repeat until feasible 
		rand_circ_digraph(G, degree);
		/* Compute connectivity */
		digraph_connectivity(G);
		if (G->attrs.k > f) 
			break;
	}
	
	/* Compute depth */
	ssp_count = digraph_fault_diameter(G, best_sol.obj_func.DfU, best_sol.obj_func.lpc); 
	*avail_ssp_count -= ssp_count;
	evals++;
	if (ssp_count < n-degree-1) {
		/* The evaluation was interrupted by the upper bound */
		return;
	}
	if (stats) {
		opt_env.sol_array[opt_env.sol_count].obj_func.DfU = G->attrs.DfU;
		opt_env.sol_array[opt_env.sol_count].obj_func.lpc = G->attrs.lpc;
	}
	opt_env.sol_count++;
	
	if (debug) {
		info("   G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
		for (j = 1; j < G->degree; j++) {
			info(",%"PRIu32, G->S[j]);
		}
		info("]): DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
				G->attrs.DfL, G->attrs.DfU, G->attrs.lpc, G->attrs.k);
	}
	
	if ( (G->attrs.DfU < best_sol.obj_func.DfU) ||
		 ((G->attrs.DfU == best_sol.obj_func.DfU) && 
		 (G->attrs.lpc <=  best_sol.obj_func.lpc)) )
	{
		/* At least as good as before; keep it */
		best_sol.obj_func.DfU = G->attrs.DfU;
		best_sol.obj_func.lpc = G->attrs.lpc;
		best_sol.obj_func.DfL = G->attrs.DfL;             
		copy_digraph(G, best_sol.G);
	}

	/* Hill climbing */
	prev = 0;
	same_sol_count = 0;
	while ( (evals < sample_count) && 
			(same_sol_count < max_same_sol_count) &&
			(*avail_ssp_count > 0) ) 
	{
		/* Mutate previous solution */
		same_sol_count++;
		copy_digraph(opt_env.G[prev], opt_env.G[!prev]);
		G = opt_env.G[!prev];
		*avail_ssp_count -= (*mutate)(G);
		
		/* Compute connectivity */
		digraph_connectivity(G);
		if (G->attrs.k <= f) {
			//~ if (debug) {
				//~ info("   mG=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
				//~ for (j = 1; j < G->degree; j++) {
					//~ info(",%"PRIu32, G->S[j]);
				//~ }
				//~ info("]): infeasible k=%"PRIu32"\n", G->attrs.k);
			//~ }
			continue;
		}
		
		/* Compute depth */
		ssp_count = digraph_fault_diameter(G, best_sol.obj_func.DfU, best_sol.obj_func.lpc); 
		*avail_ssp_count -= ssp_count;
		if (ssp_count < n-degree-1) {
			continue;
		}
		if (stats) {
			opt_env.sol_array[opt_env.sol_count].obj_func.DfU = G->attrs.DfU;
			opt_env.sol_array[opt_env.sol_count].obj_func.lpc = G->attrs.lpc;
		}
		opt_env.sol_count++;

		if (debug) {
			info("      mG=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
			for (j = 1; j < G->degree; j++) {
				info(",%"PRIu32, G->S[j]);
			}
			info("]): DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
				G->attrs.DfL, G->attrs.DfU, G->attrs.lpc, G->attrs.k);
		}
		
        if ( (G->attrs.DfU < best_sol.obj_func.DfU) ||
             ((G->attrs.DfU == best_sol.obj_func.DfU) && 
             (G->attrs.lpc <=  best_sol.obj_func.lpc)) )
        {
			/* At least as good as before; keep it */
            best_sol.obj_func.DfU = G->attrs.DfU;
            best_sol.obj_func.lpc = G->attrs.lpc;
            best_sol.obj_func.DfL = G->attrs.DfL;            
            copy_digraph(G, best_sol.G);
            
			prev = !prev;
			same_sol_count = 0;
		}
    }
}

#endif
