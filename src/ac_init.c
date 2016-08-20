/**                                                                                                      
 * AllConcur 
 * 
 * Initialization
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

#include <debug.h>
#include <mpfr.h>

#include <allconcur.h>
#include <messages.h>
#include <ctrl_sm.h>
#include <ac_init.h>

/* ================================================================== */
/* Type definitions */
#if 1

#define GS_DIGRAPH

#endif

/* ================================================================== */
/* Global variables */
#if 1

/* Failure data from TSUBAME2.5 */
static const uint32_t mpfr_prec = 250;
static const double node_afr = 47.85839160839161;
static const double node_mttf = 18304;
static const uint32_t node_delta =  24;

#endif

/* ================================================================== */
/* Local functions - prototypes */
#if 1

static int 
init_data(uint32_t n);
static int 
update_size(uint32_t n);
static int 
update_degree(uint32_t n, uint32_t rnines);
static int 
parse_server_file(char *filename);

static void 
binom_coeff(mpfr_t bc, uint32_t n, uint32_t k);
static void 
test_binom_coeff();
static inline double 
afr2mttf(double afr);
static void 
failure_prob(mpfr_t p, double mttf, uint32_t delta);
static void 
test_failure_prob();
static uint32_t 
fault_tolerance(uint32_t n, int r_nines, uint32_t delta);
static uint32_t 
compute_digrap_degree(uint32_t n, uint32_t rnines);

#endif

/* ================================================================== */
/* Global functions */
#if 1

int ac_init(uint32_t n, uint32_t rnines)
{
    int rv, i;
    
    /* Initialize data */
    rv = init_data(n);
    if (0 != rv) {
        error("init_data\n");
        return 1;
    }
    
    info_wtime("Myself [p%"PRIu32"] %s:%s:%s:%s\n", data.self, 
            data.self_ni.host, data.self_ni.ac_port, 
            data.self_ni.fd_port, data.clt_port);
    
    /* Update degree -- it create a new digraph */
    rv = update_degree(n, rnines);
    if (0 != rv) {
        error("update_degree\n");
        return 1;
    }
        
    return 0;
}

int update_digraph(uint32_t n, uint32_t rnines)
{    
    if (0 != update_size(n)) {
        error("update_size\n");
        return 1;
    }
    
    if (0 != update_degree(n, rnines)) {
        error("update_degree\n");
        return 1;
    }
    
    /* Update size and reliability */
    data.n = n;
    
    return 0;
}

void ac_destroy()
{
    srv_t *srv;
    client_t *clt;
    sid_queue_t *q;
    ep_t *ep;
    uint32_t i;
        
    /* Free g array */
    g_array_free(data.g_array);
 
    /* Free list of clients */
    info_wtime("Disconnecting clients\n");
    while (NULL != (ep = data.client_list)) {
        data.client_list = ep->next;
        ac_ep_destroy(ep);
    } 
 
    /* Free list of predecessors */
    info_wtime("Disconnecting predecessors\n");
    while (NULL != (ep = data.prev_srv_list)) {
        data.prev_srv_list = ep->next;
        ac_ep_destroy(ep);
    }
         
    /* Free list of successors */
    info_wtime("Disconnecting successors\n");
    while (NULL != (ep = data.next_srv_list)) {
        data.next_srv_list = ep->next;
        ac_ep_destroy(ep);
    }
    
    if (ac_net_mod->wait_for_disconnects) {
        info_wtime("Waiting for client disconnections\n");
        ac_net_mod->wait_for_disconnects(data.client_ch);
        info_wtime("Waiting for predecessor disconnections\n");
        ac_net_mod->wait_for_disconnects(data.prev_srv_ch);
        info_wtime("Waiting for successor disconnections\n");
        ac_net_mod->wait_for_disconnects(data.next_srv_ch);
    }
    
    /* Destroy client SM -- KVS */
#ifdef AC_KVS
    destroy_kvs_ht(data.kvs);
    data.kvs = NULL;
#endif    
    
    /* Destroy control SM */
    destroy_kvs_ht(data.ctrl_sm);
    data.ctrl_sm = NULL;
    
    /* Destroy both digraphs */
    destroy_digraph(&data.G[0]);
    destroy_digraph(&data.G[1]);
    
    /* Free digraph environment */
    free_digraph_env();
    
    /* Free tuple queue (used in the algorithm) */
    if (NULL != tuple_queue) {
        free(tuple_queue);
        tuple_queue = NULL;
    }
    
    /* Free array that indicates the already sent messages */
    if (data.sent_msgs) {
        free(data.sent_msgs);
        data.sent_msgs = NULL;
    }
    
    /* Destroy request pool */
    rp_destroy(&data.request_pool);
    
    /* Free vertexes to servers map */
    if (NULL != data.vertex_to_srv_map) {
        for (i = 0; i < data.n; i++) {
            srv = &data.vertex_to_srv_map[i];
            /* Free input */
            if (NULL != srv->input) {
                free(srv->input);
                srv->input = NULL;
            }
            /* Free list of failure notifications */
            while ((q = srv->fn) != NULL) {
                srv->fn = q->next;
                free(q);    
            }
        }
        free(data.vertex_to_srv_map);
        data.vertex_to_srv_map = NULL;
    }
}

#endif

/* ================================================================== */
/* Local functions */
#if 1

static int 
init_data(uint32_t n)
{
    int rv;
    
    data.activeG = 1;
    
    /* Init number of servers and allocate vertexes to servers map */
    data.n = n;
    data.vertex_to_srv_map = (srv_t*)malloc(n*sizeof(srv_t));
    if (NULL == data.vertex_to_srv_map) {
        error("cannot allocate vertex_to_srv_map\n");
        return 1;
    }
    memset(data.vertex_to_srv_map, 0, n*sizeof(srv_t));
    if (join) {
        /* Remap digraph vertexes to servers */
        rv = remap_vertexes_to_servers(data.ctrl_sm, 
                            data.vertex_to_srv_map, data.n);
        if (0 != rv) {
            error("remap_vertexes_to_servers\n");
            return 1;
        }
    }
    else {   
        /* Create control SM */
        if (NULL == data.ctrl_sm) {
            data.ctrl_sm = new_ctrl_sm();
            if (NULL == data.ctrl_sm) {
                error("new_ctrl_sm\n");
                return 1;
            }
        }
    
        /* Parse server file */
        if (data.srv_file) {
            rv = parse_server_file(data.srv_file);
            if (0 != rv) {
                error("parse_server_file\n");
                return 1;
            }
            free(data.srv_file);
        }
    
#ifdef AC_KVS
        /* Create client SM -- KVS */
        if (NULL == data.kvs) {
            data.kvs = create_kvs_ht(0);
            if (NULL == data.kvs) {
                error("create_kvs_ht\n");
                return 1;
            }
        }
#endif
    }
    
    /* Init the request pool */
    rp_init(&data.request_pool);
    
    return 0;
}

static int 
parse_server_file(char *filename)
{
    int rv;
    uint32_t sid;
    char line[LINE_MAX];
    char *word;
    FILE *stream = NULL;
    srv_t *srv = data.vertex_to_srv_map;
    srv_value_t srv_value;
    
    stream = fopen(filename, "r");
    if (NULL == stream) {
        error("cannot open server file %s\n", filename);
        return 1;
    }
    if (NULL == data.ctrl_sm) {
        error("no control SM\n");
        fclose(stream);
        return 1;
    }
    if (NULL == srv) {
        error("no vertex_to_srv_map\n");
        fclose(stream);
        return 1;
    }
    while (fgets(line, LINE_MAX, stream)) { 
        /* Parse each line */
        if (line[0] == '#') continue;
        if (line[0] == '\n') continue;
        /* Remove trailing newline */
        line[strcspn(line, "\r\n")] = 0;

        memset(&srv_value, 0, sizeof(srv_value_t));
               
        /* host */
        word = strtok(line," \t\r\n");
        strcpy(srv_value.ni.host, word);
        
        /* allconcur port */
        word = strtok(NULL, " \t\r\n");
        strcpy(srv_value.ni.ac_port, word);
        
        /* FD port */
        word = strtok(NULL, " \t\r\n");
        strcpy(srv_value.ni.fd_port, word);

        /* Add server to CTRL SM */
        if (1 > add_server_to_ctrl_sm(data.ctrl_sm, &srv_value)) {
            error("add_server_to_ctrl_sm\n");
            fclose(stream);
            return 1;
        }
    }
    
    /* Remap digraph vertexes to servers */
    rv = remap_vertexes_to_servers(data.ctrl_sm, srv, data.n);
    if (0 != rv) {
        error("remap_vertexes_to_servers\n");
        fclose(stream);
        return 1;
    }
    /* Set own sid */
    for (sid = 0; sid < data.n; sid++) {
        if ( (strcmp(data.self_ni.host, 
                                srv[sid].srv_value->ni.host) == 0) &&
            (strcmp(data.self_ni.ac_port, 
                                srv[sid].srv_value->ni.ac_port) == 0) )
        {
            data.self = sid;
            break;
        }
    }
    if (sid == data.n) {
        info("Not part of the new remapping... bye bye\n");
        fclose(stream);
        return 1;
    }

    /* Close file */
    fclose(stream);
    return 0;
}

static int 
update_size(uint32_t n)
{
    srv_value_t *srv_value;
    sid_queue_t *sq, *q;
    int rv;
    uint32_t sid;
    
    if (data.n == n) return 0;
    
    /* Remap vertexes to servers: first, free previous data... */
    for (sid = 0; sid < data.n; sid++) {
        /* Free input */
        if (NULL != data.vertex_to_srv_map[sid].input) {
            free(data.vertex_to_srv_map[sid].input);
            data.vertex_to_srv_map[sid].input = NULL;
        }
        /* Free list of failure notifications */
        sq = data.vertex_to_srv_map[sid].fn;
        while ((q = sq) != NULL) {
            sq = q->next;
            free(q);    
        }
        /* The srv_value is freed when destroying the control SM */
    }
    /* ...and then remap */
    data.vertex_to_srv_map = (srv_t*)
            realloc(data.vertex_to_srv_map, n * sizeof(srv_t));
    if (NULL == data.vertex_to_srv_map) {
        error("allocating vertex_to_srv_map\n");
        return 1;
    }
    memset(data.vertex_to_srv_map, 0, n * sizeof(srv_t));
    rv = remap_vertexes_to_servers(data.ctrl_sm, 
                              data.vertex_to_srv_map, n);
    if (0 != rv) {
        error("remap_vertexes_to_servers\n");
        return 1;
    }
    for (sid = 0; sid < n; sid++) {
        srv_value = data.vertex_to_srv_map[sid].srv_value;
        if ( (strcmp(data.self_ni.host, srv_value->ni.host) == 0) &&
            (strcmp(data.self_ni.ac_port, srv_value->ni.ac_port) == 0) )
        {
            data.self = sid;
            break;
        }
    }
    if (sid == n) {
        info("Not part of the new remapping... bye bye\n");
        terminate(0);
    }  

    return 0;
}

static int 
update_degree(uint32_t n, uint32_t rnines)
{
    char g_name[64];
    digraph_t *G = NULL;
    send_buf_t *sb;
    ep_t *ep;
    int rv;
    uint32_t degree, f, i, prev_degree = 0;
    
    TIMER_INIT;
    
    if ((data.n == n) && (data.rnines == rnines)) return 0;
    
    /* Compute previous degree */
    if (data.G[data.activeG]) {
        prev_degree = data.G[data.activeG]->degree;
    }

    /* Initialize digraph environment; 
       necessary for each size modification */
    init_digraph_env(n);

#ifdef GS_DIGRAPH   
    /* Recompute fault tolerance */
    f = fault_tolerance(n, rnines, node_delta);
    degree = f+1;
    if (degree > n-1) {
        info("Cannot offer %"PRIu32"-nines reliability with %"PRIu32" servers; \n", rnines, n);
 goto complete_graph;
        terminate(1);
    }
    
    /* Create Gs-digraph */
    if (timer) {
        TIMER_START("Creating Gs-digraph: n=%"PRIu32
            ", d=%"PRIu32", f=%"PRIu32" ... ", n, degree, f);
    }
    else {
        info("Creating Gs-digraph: n=%"PRIu32
            ", d=%"PRIu32", f=%"PRIu32" ... ", n, degree, f);
    }
    G = create_sim_digraph(degree, 0);
#if 0
    /* Compute diameter */
    digraph_diameter(G);
    info("   -> D=%d (Dmin=%d)\n", G->attrs.D, 
            min_diameter(n, degree));
    /* Compute fault diameter */
    digraph_fault_diameter(G, UINT32_MAX, 0);
    info("   ->DfL=%"PRIu32"; DfU=%"PRIu32"(#%"PRIu32")\n", 
        G->attrs.DfL, G->attrs.DfU, G->attrs.lpc);
    //if (0 == data.self) {
    //    sprintf(g_name, "digraph_n%"PRIu32, n);
    //    digraph2dot(G, g_name);
    //}
    print_digraph(G);
#endif
#else  
    /* Create binomial graph */
    if (timer) {
        TIMER_START("Creating binomial graph: n=%"PRIu32" ... ", n);
    }
    else {
        info("Creating binomial graph: n=%"PRIu32" ... ", n);
    }
    G = new_binomial_graph();
    if (G) {
        degree = G->degree;
        f = degree-1;
        info("(degree=%"PRIu32", f=%"PRIu32") ", degree, f);
    }
#endif     
complete_graph:    
    if (!G) {
        info("Warning: create K%"PRIu32" instead\n", n);
        G = create_complete_digraph();
        degree = n - 1;
        f = n-1;
    }
    /* Set digraph's fault tolerance */
    set_digraph_ft(G, f);
    /* Activate the newly create digraph */
    data.activeG = !data.activeG;
    destroy_digraph(&data.G[data.activeG]);
    data.G[data.activeG] = G;

    if (timer) {
        TIMER_STOP;
    }
    else {
        info("done\n");
    }

    /* Reallocate space for the array for sent messages */
    data.sent_msgs = (uint8_t*)
                        realloc(data.sent_msgs, (degree+1)*n);
    if (NULL == data.sent_msgs) {
        error("allocating sent_msgs\n");
        return 1;
    }
    memset(data.sent_msgs, 0, (degree+1)*n);
    
    /* Reallocate space for tuple queue */
    tuple_queue = (tuple_t*)malloc(degree*degree*sizeof(tuple_t));
    if (NULL == tuple_queue) {
        error("allocating tuple_queue\n");
        return 1;
    }

    /* Free (outdated) list of successors */
    while (NULL != (ep = data.next_srv_list)) {
        data.next_srv_list = ep->next;
        ac_ep_destroy(ep);
    }
    
    /* Free (outdated) list of predecessors */
    while (NULL != (ep = data.prev_srv_list)) {
        data.prev_srv_list = ep->next;
        ac_ep_destroy(ep);
    }
                            
    data.rnines = rnines;
    
    return 0;
}

/* ================================================================== */

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
    //mpfr_fprintf (dbg_stream, "p = %0.120RDf\n", p);
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
    //mpfr_fprintf (dbg_stream, "p = %0.120RDf\n", p);
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
//mpfr_fprintf(dbg_stream, "r(f=%d) = %0.120RDf\n", f, r);
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
static uint32_t 
compute_digrap_degree(uint32_t n, uint32_t rnines)
{    
    return fault_tolerance(n, rnines, node_delta) + 1;
}

#endif
