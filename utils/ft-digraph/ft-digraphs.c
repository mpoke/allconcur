/**                                                                                                      
 * Fault tolerant circulant digraphs
 * 
 * Main file
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
#include <debug.h>

//#include <gmp.h>
#include <mpfr.h>

#include <digraph.h>
#include <da_maxflow.h>  
#include <fib.h>
#include <ssp.h>
#include <timer.h>
#include <opt.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define RUN_OPTIMIZATION	1
#define RUN_BG 				2
#define RUN_FEASIBILITY		3
#define RUN_SIM				4

#endif

/* ================================================================== */
/* Global variables */
#if 1

FILE *dbg_stream, *out;
unsigned long long g_timerfreq;
static const uint32_t mpfr_prec = 250;
static const double node_afr = 47.85839160839161;
static const double node_mttf = 18304;
static const uint32_t node_delta =  24;
int timer;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static void 
usage(char *prog);
static void 
int_handler(int);
static void 
terminate(int ret);

static void 
binom_coeff(mpfr_t bc, uint32_t n, uint32_t k);
static void 
test_binom_coeff();
static int 
low_search_space(uint32_t n, uint32_t k);

static inline double 
afr2mttf(double afr);
static void 
failure_prob(mpfr_t p, double mttf, uint32_t delta);
static void 
test_failure_prob();

static uint32_t
fault_tolerance(uint32_t n, int rr, uint32_t delta);
static void
test_fault_tolerance();

static uint32_t
reliability(uint32_t n, uint32_t k, uint32_t delta);
static void
test_reliability();

#endif

/* ================================================================== */
/* Global functions */
#if 1

int main(int argc, char* argv[])
{
	HRT_TIMESTAMP_T t1, t2;
	uint64_t ticks;
    double elapsed_time;
    
	uint32_t n = 0, degree = 0, r_nines = 6, f;
    int c, i, j;
    static int run_type = RUN_OPTIMIZATION;
    char *out_file="", *s = NULL;
    
#if 0 // test some local functions
	test_binom_coeff();
	test_failure_prob();
	test_fault_tolerance();
	test_reliability();
	return 0;
#endif 	    
    
    dbg_stream = stdout;
    
    /* Parse command line */
    while (1) {
        static struct option long_options[] = {
			/* These options set the type of run */
            {"opt", no_argument, &run_type, RUN_OPTIMIZATION},
            {"bg",  no_argument, &run_type, RUN_BG},
            {"fsb",   no_argument, &run_type, RUN_FEASIBILITY},
            {"sim",   no_argument, &run_type, RUN_SIM},
            /* Flag for timer */
            {"timer", no_argument, &timer, 1},
            {0, 0, 0, 0}
        };
        int option_index = 0;
        c = getopt_long (argc, argv, "hn:d:o:r:",
                       long_options, &option_index);
        /* Detect the end of the options. */
        if (c == -1) break;

        switch (c) {
            case 0:
                /* If this option set a flag, do nothing else now. */
                if (long_options[option_index].flag != 0)
                    break;
                printf("option %s", long_options[option_index].name);
                if (optarg)
                    printf (" with arg %s", optarg);
                printf("\n");
                break;

            case 'h':
                usage(argv[0]);
                exit(1);
                
            case 'n':
				n = (uint32_t)atoi(optarg);
                break;
                
            case 'd':
                degree = (uint32_t)atoi(optarg);
                break;
            
            case 'r':
                r_nines = (uint32_t)atoi(optarg);
                break;
                
            case 'o':
                out_file = optarg;
                break;

            case '?':
                break;

            default:
                exit(1);
        }
    }   
	
#if 1 // DEBUGGING	
	init_digraph_env(n);

    //~ digraph_t *bG = new_binomial_graph();
    //~ graph2dot(bG, "bg");
    //~ print_digraph(bG);
	//~ digraph_connectivity(bG);
	//~ info("Connectivity: %d\n", bG->attrs.k);
	//~ set_digraph_ft(bG, bG->attrs.k-1);
	//~ digraph_diameter(bG);
	//~ info("Diameter: %d (min=%d)\n", 
		//~ bG->attrs.D, min_diameter(env.n, bG->degree));
	//~ digraph_fault_diameter(bG, UINT32_MAX, 0);
	//~ info("DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
			//~ bG->attrs.DfL, bG->attrs.DfU, bG->attrs.lpc);
    //~ destroy_digraph(&bG);
    //~ terminate(0);
    
	/* Test regular digraph */
	//~ digraph_t *G = new_digraph();
	//~ info("n=%d, d=%d\n", n, degree);
	//~ rand_digraph(G, degree);
	//~ print_digraph(G);
	//~ digraph_connectivity(G);
	//~ info("Connectivity: %d\n", G->attrs.k);
	//~ digraph_diameter(G);
	//~ info("Diameter: %d (min=%d)\n", 
		//~ G->attrs.D, min_diameter(env.n, G->degree));
	//~ set_digraph_ft(G, G->attrs.k-1);
	//~ digraph_fault_diameter(G, UINT32_MAX, 0);
	//~ info("DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
			//~ G->attrs.DfL, G->attrs.DfU, G->attrs.lpc);
	//~ destroy_digraph(&G);
	
	/* Test sim digraph */
    char name[64];
	f = fault_tolerance(n, r_nines, node_delta);
	degree = f+1;
	info("Create SIM-digraph: n=%d, d=%d, f=%d\n", n, degree, f);
	digraph_t *simG;
    simG = create_sim_digraph(degree, 0);
    if (NULL == simG) terminate(1);
    
    //~ sprintf(name, "gs_n%"PRIu32"_d%"PRIu32, n, degree);
    //~ digraph2dot(simG, name);
    //print_digraph(simG);
	//~ 
    set_digraph_ft(simG, f);
	digraph_diameter(simG);
	info("Diameter: %d (min=%d)\n", 
		simG->attrs.D, min_diameter(env.n, simG->degree));
	//~ digraph_fault_diameter(simG, UINT32_MAX, 0);
	//~ info("DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
			//~ simG->attrs.DfL, simG->attrs.DfU, simG->attrs.lpc);
	
	destroy_digraph(&simG);
	
	/* Test circulant graph */
	//~ circ_digraph_t *cG = new_circ_digraph();
    //~ f = fault_tolerance(n, r_nines, node_delta);
	//~ degree = f+1;
	//~ while (1) {
		//~ rand_circ_digraph(cG,degree);
		//~ digraph_connectivity(cG);
		//~ if (cG->attrs.k == degree) break;
	//~ }
	//~ print_digraph(cG);
	//~ digraph2dot(cG, "circ");
	//~ 
	//~ digraph_connectivity(cG);
	//~ info("Connectivity: %d\n", cG->attrs.k);
	//~ digraph_diameter(cG);
	//~ info("Diameter: %d (min=%d)\n", 
		//~ cG->attrs.D, min_diameter(env.n, cG->degree));
	//~ digraph_fault_diameter(cG, UINT32_MAX, 0);
	//~ info("   DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
			//~ cG->attrs.DfL, cG->attrs.DfU, cG->attrs.lpc);
	//~ 
	//~ destroy_digraph(&cG);
	
	terminate(0);
#endif	
	
#if 1 // Check reliability 	
	if (r_nines < 1) {
        printf("Error: reliability must be at least 90%% (1-nine)\n");
        exit(1);
    }
       
    /* Compute vertex failure probability */
    mpfr_t p;
	mpfr_init2(p, mpfr_prec);
	failure_prob(p, afr2mttf(node_afr), node_delta);
    //~ info("##########\n");
    //~ info("A node's AFR = %4.2lf%%.\n", node_afr);
    //~ info("A node's probability to fail in %d hours is", node_delta);
    //~ mpfr_fprintf(dbg_stream, " %.10RDf.\n", p);
    
    f = fault_tolerance(n, r_nines, node_delta);
    /* Check if f < n */
    if (f > n) {
        info("Error: a %d-node network with node's AFR = %4.2lf%% "
				"cannot have %"PRIu32"-nines reliability\n", 
				n, node_afr, r_nines);
        exit(1);
    }
    if (degree && (f >= degree)) {
		info("Error: a %d-node network with node's AFR = %4.2lf%% "
				"needs a minimum degree of %"PRIu32" for %"
				PRIu32"-nines reliability\n", n, node_afr, f, r_nines);
        exit(1);
	}
    //~ info("For a %d-node network to have %"PRIu32"-nines reliability,"
		//~ " it must tolerate at least %d failures.\n\n", n, r_nines, f);
    mpfr_clear(p);
#endif
	
	/* Open data file */
    if (strcmp(out_file, "") == 0) {
        out_file = "data.out";
    }
    out = fopen(out_file, "w+");
    if (NULL == out) {
        info("Cannot open output file\n");
        exit(1);
    }
    
    /* Set handler for SIGINT */
    signal(SIGINT, int_handler);
    
	/* Initialize timer */
    if (timer)  {
        info("Init timer...");fflush(stdout);
        HRT_INIT(g_timerfreq);
        info("done\n");
    }
    
    /* Initialize environment: 
     * allocate memory for the maximum graph size */
    init_digraph_env(n);
    
    
    obj_func_t ub;
    digraph_t *G, *rndG;
    uint32_t max_r_nines, max_f;
    switch (run_type) {
		case RUN_OPTIMIZATION:
		{
			if (0 == degree) degree = f + 1;
			info("Optimization run: n=%d, degree=%d, f=%d\n", 
				n, degree, f);
			
			ub.DfU = UINT32_MAX;
			ub.DfL= 0;
			ub.lpc = 0;
			if (low_search_space(n-1, degree)) {
				optimize(n, degree, f, ub, OPT_EXAUST);
			} else {
				optimize(n, degree, f, ub, OPT_RAND);
				//~ optimize(n, degree, f, OPT_CMP_RAND_HILL);
			}
			break;
		}
		case RUN_BG:
		{
			G = new_binomial_graph();
			//~ f = G->degree-1;
			set_digraph_ft(G, f);
			info("Compare with the binomial graph: n=%d, degree=%d, f=%d\n", 
				n, G->degree, f);
			print_digraph(G);
			digraph_connectivity(G);
			info("   -> k: %"PRIu32"\n", G->attrs.k);
			max_r_nines = reliability(env.n, G->attrs.k, node_delta);
			if (r_nines > max_r_nines) {
				info("   -> cannot achieve the required reliability;"
					" maximum is %"PRIu32"-nines\n", max_r_nines);
				break;
			}
			info("   -> maximum reliability: %"PRIu32"-nines\n", max_r_nines);
			max_f = fault_tolerance(env.n, max_r_nines, node_delta);
			info("   -> maximum fault-tolerance: %"PRIu32"\n", max_f);
			digraph_diameter(G);
			info("   -> D=%d (min=%d)\n", 
					G->attrs.D, min_diameter(env.n, G->degree));
			digraph_fault_diameter(G, UINT32_MAX, 0);
			info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
						G->attrs.DfL, G->attrs.DfU, G->attrs.lpc);
			
			ub.D = G->attrs.D;			
			ub.DfU = G->attrs.DfU;
			ub.DfL= G->attrs.DfL;
			ub.lpc = G->attrs.lpc;
			optimize(n, G->degree, f, ub, OPT_RAND);
			destroy_digraph(&G);
			break;
		}
		case RUN_SIM:
		{
			degree = f+1;
			if (degree < 3) {
				info("Error: the degree of the SIM graph must be at least 3\n");
				terminate(1);
			}
			if (env.n < 2*degree) {
				info("Error: the degree of the SIM graph must be at most n/2\n");
				terminate(1);
			}
			if (timer) HRT_GET_TIMESTAMP(t1);
			G = create_sim_digraph(degree, 0);
			set_digraph_ft(G, f);
			info("SIM digraph (n=%d, degree=%d, f=%d)\n", 
				n, G->degree, f);
			
			digraph_diameter(G);
			info("   -> D=%d (Dmin=%d)\n", 
					G->attrs.D, min_diameter(env.n, G->degree));
					
			digraph_fault_diameter(G, UINT32_MAX, 0);
			info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
						G->attrs.DfL, G->attrs.DfU, G->attrs.lpc);
			if (timer) {
				HRT_GET_TIMESTAMP(t2);
				HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
				elapsed_time = HRT_GET_SEC(ticks);
				info("...done (%lf s)\n", elapsed_time);
			}
			
			/* Compare to circular digraphs */		
			//~ ub.D = G->attrs.D;
			//~ ub.DfU = G->attrs.DfU;
			//~ ub.DfL= G->attrs.DfL;
			//~ ub.lpc = G->attrs.lpc;
			//~ optimize(n, G->degree, f, ub, OPT_RAND);
			
			/* Compare to regular digraphs */
			rndG = new_digraph();
			set_digraph_ft(rndG, f);
			info("\nRandom regular digraphs:\n");
			for (i = 0; i < 10; i++) {
				rand_digraph(rndG, degree);
				//~ print_digraph(G);
				digraph_connectivity(rndG);
				info("   -> k=%d\n", rndG->attrs.k);
				digraph_diameter(rndG);
				info("   -> D=%d (Dmin=%d)\n", 
					rndG->attrs.D, min_diameter(env.n, G->degree));
				digraph_fault_diameter(rndG, UINT32_MAX, 0);
				info("   -> DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n\n", 
						rndG->attrs.DfL, rndG->attrs.DfU, rndG->attrs.lpc);
			}
			destroy_digraph(&rndG);
						
			destroy_digraph(&G);
		}
		default: terminate(0);
	}   
        
	terminate(0);
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static void 
usage(char *prog)
{
    printf("Usage: %s [OPTIONS]\n"
            "OPTIONS:\n"
            "\t--opt | --bg | --fsb | --sim		run type\n"
			"\t\t OPTimization	 - requires n and r\n"
			"\t\t Binomial Graph - requires n, r\n"
			"\t\t FeaSiBility 	 - requires n, d, and r\n"
			"\t\t SIM Digraph 	 - requires n and r\n"
            "\t-n <size>				number of nodes\n"
            "\t-d <#offsets>          	number of offsets (degree)\n"
            "\t-r <k-nines>     		required reliability\n"
            "\t-o <output file>     	(default: data.out)\n"
            "\t--timer               	get runtime estimates\n",
            prog);
}

static void 
int_handler(int dummy) 
{
    printf("SIGINT detected; shutdown\n");
    
    terminate(1); 
}

static void 
terminate(int ret)
{
	/* Free DA environment */
	da_clean();
	
	/* Free ssp environment */
	ssp_clean();
	
	/* Free optimization environment */
	free_opt_env();
	
    /* Free environment */
    free_digraph_env();
    
    /* Close out file */
    if (NULL != out) {
		fclose(out);
		out = NULL;
	}
    
    exit(ret);
}

/**
 * Compute binomial coefficient using the MPFR library 
 */
static void 
binom_coeff(mpfr_t bc, uint32_t n, uint32_t k)
{
	mpfr_t pk, pn, tmp;

	mpfr_init2(pn, mpfr_prec);
	mpfr_init2(pk, mpfr_prec);
	mpfr_init2(tmp, mpfr_prec);
	
	mpfr_set_d(bc, 1.0, MPFR_RNDD);
	mpfr_set_ui(pn, n, MPFR_RNDD);
   
    /* Choose min between k and n-k */
    if (k > n - k) {
		mpfr_set_ui(pk, n-k, MPFR_RNDD);
	} else {
		mpfr_set_ui(pk, k, MPFR_RNDD);
	}
    
    /* C(n,k) = prod(n/j) n=n:(n-k+1); j=1:k */
    while(mpfr_cmp_ui(pk,0) > 0) {
		mpfr_div(tmp, pn, pk, MPFR_RNDD);
		mpfr_mul(bc, bc, tmp, MPFR_RNDD);
		mpfr_sub_ui(pn, pn, 1, MPFR_RNDD);
		mpfr_sub_ui(pk, pk, 1, MPFR_RNDD);
	}
	
	mpfr_clear(pk);
	mpfr_clear(pn);
	mpfr_clear(tmp);
}
static void 
test_binom_coeff()
{
	int n = 100;
	int k = 20;
	
	mpfr_t bc;
	mpfr_init2(bc, mpfr_prec);	
	binom_coeff(bc,n,k);
	if (mpfr_cmp_ui(bc,1000) > 0) {
		printf("C(%d,%d) > 1000\n", n, k);
	}
	//~ mpfr_printf ("%50.0RDf\n", bc);
	
	mpfr_clear(bc);
}

/**
 * Check whether the search space is low relatively to the sample count
 */
static int 
low_search_space(uint32_t n, uint32_t k)
{
	mpfr_t bc;
	mpfr_init2(bc, mpfr_prec);	
	binom_coeff(bc, n, k);
	if (mpfr_cmp_ui(bc, sample_count) <= 0) {
		return 1;
	}
	return 0;
}

/**
 * Compute the mean time to failure (MTTF) in hours
 * @param afr the annualized failure rate (AFR) in %
 * Note: the AFR gives the estimated probability that a device 
 * will fail during a full year of use.
 */
static inline double 
afr2mttf(double afr)
{
  return (8760*100 / afr);
}

/**
 * Compute the failure probability 
 * according to an exponential lifetime distribution model (LDM)
 * @param mttf the MTTF
 * @param delta the period of the failure probability (in hours)
 */
static void 
failure_prob(mpfr_t p, double mttf, uint32_t delta)
{
	mpfr_set_d(p, -1./mttf*delta, MPFR_RNDD);
	mpfr_exp(p, p, MPFR_RNDD);
	mpfr_ui_sub(p, 1, p, MPFR_RNDD);
}
static void 
test_failure_prob()
{
	mpfr_t p;
	mpfr_init2(p, mpfr_prec);
	//~ failure_prob(p, afr2mttf(node_afr), node_delta);
	failure_prob(p, node_mttf, node_delta);
	mpfr_printf ("%0.40RDf\n", p);
	
	mpfr_clear(p);
}

/**
 * Compute the amount of fault tolerance required
 * @param n the number of nodes
 * @param rr the required reliability (in k-nine notation)
 * @param delta the period of the failure probability (in hours)
 */
static uint32_t
fault_tolerance(uint32_t n, int r_nines, uint32_t delta)
{   
    mpfr_t p, q, r, a, b;
	mpfr_init2(p, mpfr_prec);
	mpfr_init2(q, mpfr_prec);
	mpfr_init2(r, mpfr_prec);
	mpfr_init2(a, mpfr_prec);
	mpfr_init2(b, mpfr_prec);
	mpfr_set_d(r, 0.0, MPFR_RNDD);
    
    /* Failure probability of one node */
    failure_prob(p, node_mttf, delta);
    mpfr_ui_sub(q, 1, p, MPFR_RNDD);
    
    uint32_t f;
    for (f = 0; f < n; f++) {
		mpfr_pow_ui(a,p,f,MPFR_RNDD);
		mpfr_pow_ui(b,q,n-f,MPFR_RNDD);
		mpfr_mul(a, a, b, MPFR_RNDD);
		binom_coeff(b,n,f);
		mpfr_mul(a, a, b, MPFR_RNDD);
		mpfr_add(r, r, a, MPFR_RNDD);
		
		/* Check whether R is good enough */
		//~ mpfr_printf ("r(f=%d) = %0.120RDf\n", f, r);
		mpfr_ui_sub(a, 1, r, MPFR_RNDD);
		mpfr_log10(a, a, MPFR_RNDD);
		if (mpfr_cmp_si(a,-r_nines) < 0) {
			break;
		}
	}
	
	mpfr_clear(p);
	mpfr_clear(q);
	mpfr_clear(r);
	mpfr_clear(a);
	mpfr_clear(b);
	
	return f;
}
static void
test_fault_tolerance()
{
	uint32_t n = 10000;
	uint32_t r_nines = 8;
	
	printf("n=%d, r_nines=%d, f = %d\n", n, r_nines, 
		fault_tolerance(n, r_nines, node_delta));
}

/**
 * Compute the maximum reliability of a digraph (k-nines)
 * @param n the number of nodes
 * @param k connectivity
 * @param delta the period of the failure probability (in hours)
 */
static uint32_t
reliability(uint32_t n, uint32_t k, uint32_t delta)
{
	
	
	mpfr_t p, q, r, a, b;
	mpfr_init2(p, mpfr_prec);
	mpfr_init2(q, mpfr_prec);
	mpfr_init2(r, mpfr_prec);
	mpfr_init2(a, mpfr_prec);
	mpfr_init2(b, mpfr_prec);
	mpfr_set_d(r, 0.0, MPFR_RNDD);
    
    /* Failure probability of one node */
    failure_prob(p, node_mttf, delta);
    mpfr_ui_sub(q, 1, p, MPFR_RNDD);
    
    uint32_t f;
    for (f = 0; f < k; f++) {
		mpfr_pow_ui(a,p,f,MPFR_RNDD);
		mpfr_pow_ui(b,q,n-f,MPFR_RNDD);
		mpfr_mul(a, a, b, MPFR_RNDD);
		binom_coeff(b,n,f);
		mpfr_mul(a, a, b, MPFR_RNDD);
		mpfr_add(r, r, a, MPFR_RNDD);
		//~ mpfr_printf ("r(f=%d) = %0.120RDf\n", f, r);
	}
	
	/* Find number of nines */
	mpfr_ui_sub(a, 1, r, MPFR_RNDD);
	mpfr_log10(a, a, MPFR_RNDD);
	mpfr_mul_si(a, a, -100, MPFR_RNDD);
	
	uint32_t r_nines = mpfr_get_uj(a, MPFR_RNDZ)/100;
		
	mpfr_clear(p);
	mpfr_clear(q);
	mpfr_clear(r);
	mpfr_clear(a);
	mpfr_clear(b);
	
	return r_nines;
}
static void
test_reliability()
{
	uint32_t n = 1024;
	uint32_t k = 19;
	
	printf("n=%d, k=%d, nine_count=%d\n", n, k, 
		reliability(n, k, node_delta));
}

#endif
