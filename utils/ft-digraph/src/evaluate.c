/**
 * Evaluate a circulant graph => work, depth, connectivity
 * @file evaluate.c
 * @author mpoke
 */
#if 0
#include <stdlib.h>
#include <unistd.h>
#include <getopt.h>
#include <math.h>
#include <signal.h>
#include <limits.h>

#include <circ_graph.h>
#include <da_maxflow.h> 
#include <fib.h>
#include <timer.h>
#include <debug.h>


#define EVALUATE
//~ #define MUTATE
#ifdef MUTATE
#undef EVALUATE
#endif
#ifdef DEBUG
#undef MUTATE
#undef EVALUATE
#endif



static uint32_t 
exhaustive_search( uint32_t m, 
                   uint32_t f, 
                   FILE* data, 
                   solution_t* solutions );
               
static int 
test_fib_heap();



int main(int argc, char* argv[])
{
    unsigned long long sol_space_size;
    solution_t *sol_array = NULL, *sol_ptr = NULL, *best_sol;
    long double p, reliab;
    uint32_t n = 0, m = 0, i, j, f, rr=4;
    uint32_t sol_count, min_count;
    int c;
    char *out_file="";
    
  
#ifdef EVALUATE
    uint32_t avg_iter;         
           
#if 0 /* Exhaustive search */
    if (timer) HRT_GET_TIMESTAMP(t1);
    printf("\nExhaustive search...\n");
    avg_iter = 0;
    for (i = 0; i < repeat_count; i++) {
        sol_count = exhaustive_search(m, f, out, sol_array);
        //~ sol_count = exhaustive_search(m, f, NULL, sol_array);
        best_sol = sol_array;
        printf("   Found D* = %"PRIu32"(#%"PRIu32")\n", 
                best_sol->D, best_sol->lp_count);
    }
    if (timer) {
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        elapsed_time = HRT_GET_SEC(ticks);
        printf("...done (%lf s)\n", elapsed_time);
    }
#endif 
    
    if (sol_array) free(sol_array);
#endif

#ifdef MUTATE
    m = f+1;
    circ_graph_t *G = new_circ_graph();
    circ_graph_t *mutated_G = new_circ_graph();
    set_circ_graph_ft(G, f);

#if 0    
    double rand_improve = 0, greedy_improve = 0;
    for (i = 0; i < sample_count; i++) {
        /* Generate random graph */
        while (1) { // repeat until feasible 
            rand_circ_graph(G, m);
            circ_graph_k(G);
            if (G->attrs.k > f) 
                break;
        }
        circ_graph_depth(G, UINT32_MAX, 0);
        //~ printf("G=(%"PRIu32",[ ", n);
        //~ for (j = 0; j < G->degree; j++) {
            //~ printf("%"PRIu32" ", G->S[j]);
        //~ }
        //~ printf("]): D=%"PRIu32"(#%"PRIu32")\n", 
            //~ G->attrs.DfU, G->attrs.lpc);
        //~ printf("Minimum improvement:");
        //~ for (j = 0; j < env.n; j++) {
            //~ printf(" %"PRIu32, G->improve[j]);
        //~ }
        //~ printf("\n");

        /* Add random offset */
        copy_circ_graph(G, mutated_G);
        add_offset_rand(mutated_G);
        circ_graph_depth(mutated_G, UINT32_MAX, 0);
        if ( (G->attrs.DfU < mutated_G->attrs.DfU) || 
             ((G->attrs.DfU == mutated_G->attrs.DfU) && 
             (G->attrs.lpc < mutated_G->attrs.lpc)) )
        {
            rand_improve += 0;
        } else {
            rand_improve += (G->attrs.DfU - mutated_G->attrs.DfU)*(f+1)*(env.n-1) 
                        + (G->attrs.lpc - mutated_G->attrs.lpc);
        }
                        
        /* Add greedy offset */
        copy_circ_graph(G, mutated_G);
        add_offset_greedy(mutated_G);
        circ_graph_depth(mutated_G, UINT32_MAX, 0);
        if ( (G->attrs.DfU < mutated_G->attrs.DfU) || 
             ((G->attrs.DfU == mutated_G->attrs.DfU) && 
             (G->attrs.lpc < mutated_G->attrs.lpc)) )
        {
            greedy_improve += 0;
        } else {
            greedy_improve += (G->attrs.DfU - mutated_G->attrs.DfU)*(f+1)*(env.n-1) 
                        + (G->attrs.lpc - mutated_G->attrs.lpc);
        }
    }
    rand_improve /= sample_count;
    greedy_improve /= sample_count;
    printf("Add random offset: average improvement = %lf\n", rand_improve);
    printf("Add greedy offset: average improvement = %lf\n", greedy_improve);
#endif 

#if 1   
    double rand_improve = 0, greedy_improve = 0;
    uint32_t rand_infeasible = 0, greedy_infeasible = 0;
    for (i = 0; i < sample_count; i++) {
        /* Generate random graph */
        while (1) { // repeat until feasible 
            rand_circ_graph(G, m);
            circ_graph_k(G);
            if (G->attrs.k > f) 
                break;
        }
        circ_graph_depth(G, UINT32_MAX, 0);
        //~ printf("G=(%"PRIu32",[ ", n);
        //~ for (j = 0; j < G->degree; j++) {
            //~ printf("%"PRIu32" ", G->S[j]);
        //~ }
        //~ printf("]): D=%"PRIu32"(#%"PRIu32") k=%"PRIu32"\n", 
            //~ G->attrs.DfU, G->attrs.lpc, G->attrs.k);
        //~ printf("Minimum improvement:");
        //~ for (j = 0; j < env.n; j++) {
            //~ printf(" %"PRIu32, G->improve[j]);
        //~ }
        //~ printf("\n");

        /* Add random offset */
        copy_circ_graph(G, mutated_G);
        add_offset_greedy(mutated_G);
        circ_graph_depth(mutated_G, UINT32_MAX, 0);
        rm_offset_rand(mutated_G, 1);
        circ_graph_k(mutated_G);
        if (mutated_G->attrs.k > f) {
            circ_graph_depth(mutated_G, UINT32_MAX, 0);
            if ( (G->attrs.DfU < mutated_G->attrs.DfU) || 
                 ((G->attrs.DfU == mutated_G->attrs.DfU) && 
                 (G->attrs.lpc < mutated_G->attrs.lpc)) )
            {
                rand_improve += 0;
            } else {
                rand_improve += (G->attrs.DfU - mutated_G->attrs.DfU)*(f+1)*(env.n-1) 
                            + (G->attrs.lpc - mutated_G->attrs.lpc);
            }
        }
        else {
            rand_infeasible++;
        }
                        
        /* Add greedy offset */
        copy_circ_graph(G, mutated_G);
        add_offset_greedy(mutated_G);
        circ_graph_depth(mutated_G, UINT32_MAX, 0);
        rm_offset_greedy(mutated_G, 1);
        circ_graph_k(mutated_G);
        if (mutated_G->attrs.k > f) {
            circ_graph_depth(mutated_G, UINT32_MAX, 0);
            if ( (G->attrs.DfU < mutated_G->attrs.DfU) || 
                 ((G->attrs.DfU == mutated_G->attrs.DfU) && 
                 (G->attrs.lpc < mutated_G->attrs.lpc)) )
            {
                greedy_improve += 0;
            } else {
                greedy_improve += (G->attrs.DfU - mutated_G->attrs.DfU)*(f+1)*(env.n-1) 
                            + (G->attrs.lpc - mutated_G->attrs.lpc);
            }
        }
        else {
            greedy_infeasible++;
        }
    }
    rand_improve /= sample_count;
    greedy_improve /= sample_count;
    printf("Remove random offset: average improvement = %lf (%d)\n", rand_improve, rand_infeasible);
    printf("Remove greedy offset: average improvement = %lf (%d)\n", greedy_improve, greedy_infeasible);
#endif 
    
    /* Destroy graph */
    destroy_circ_graph(&G);
    destroy_circ_graph(&mutated_G);
#endif

#ifdef DEBUG
    circ_graph_t *G;    
    circ_graph_t *mutated_G;
    
#if 1 // Test binomial graph
    {
    circ_graph_t *bG;
    uint32_t r, f;
    bG = get_binomial_graph();
    circ_graph_print(bG);
    circ_graph_k(bG);
    printf("   -> k = %"PRIu32"\n", bG->attrs.k);
    r = reliability(env.n, bG->attrs.k, node_delta);
    printf("   -> r >= %"PRIu32"-nines\n", r);
    f = fault_tolerance(env.n, r, node_delta);
    if (f > bG->attrs.k) {
        printf("   -> for 1-nine reliability: f = %"PRIu32"\n", f);
    }
    else printf("   -> f = %"PRIu32"\n", f);
    
    circ_graph_depth(bG, UINT32_MAX, 0);
    printf("   ->D=%"PRIu32"(#%"PRIu32")\n", bG->attrs.DfU, bG->attrs.lpc);
    
    /* Random search */
    sol_array = (solution_t*)malloc((eval_count+1)*sizeof(solution_t));
    sol_space_size = combi(env.n-1, bG->attrs.k);
    sol_count = sol_space_size > eval_count ? eval_count : sol_space_size;
    
    if (timer) HRT_GET_TIMESTAMP(t1);
    printf("Random search...\n");
    sol_count = random_search(bG->attrs.k, bG->attrs.k - 1, eval_count, out, sol_array);
    sol_ptr = sol_array+1;
    best_sol = sol_array;
    printf("solutions: %d\n", sol_count);
        
    /* Find first solution with minimum depth */
    printf("   Found D* = %"PRIu32"(#%"PRIu32")\n", 
            best_sol->D, best_sol->lp_count);
    
    /* Sort array with depth */
    qsort(sol_ptr, sol_count, sizeof(solution_t), cmpfunc_solution);
                
    /* Statistics */
    printf("   %"PRIu32"(#%"PRIu32") | %"PRIu32"(#%"PRIu32
            ") - %"PRIu32"(#%"PRIu32") - %"PRIu32"(#%"PRIu32
            ") | %"PRIu32"(#%"PRIu32")\n", 
            sol_ptr[0].D, sol_ptr[0].lp_count, 
            sol_ptr[(int)ceil(sol_count * 0.25)].D, 
            sol_ptr[(int)ceil(sol_count * 0.25)].lp_count,
            sol_ptr[(int)ceil(sol_count * 0.5)].D, 
            sol_ptr[(int)ceil(sol_count * 0.5)].lp_count,
            sol_ptr[(int)ceil(sol_count * 0.75)].D, 
            sol_ptr[(int)ceil(sol_count * 0.75)].lp_count,
            sol_ptr[sol_count-1].D, sol_ptr[sol_count-1].lp_count);
    if (timer) {
        HRT_GET_TIMESTAMP(t2);
        HRT_GET_ELAPSED_TICKS(t1, t2, &ticks);
        elapsed_time = HRT_GET_SEC(ticks);
        printf("...done (%lf s)\n", elapsed_time);
    }
             
    /* Destroy graph */
    destroy_circ_graph(&bG);
    
    fh_free_heap(&fh);
    
    /* Free environment */
    free_env();
    
    //~ fclose(depth_out);
    fclose(out);
    
    return 0; 
    }   
#endif     

    /* Allocate new graph */
    G = new_circ_graph();
    set_circ_graph_ft(G, f);    
    
#if 0 // Test specific graphs
    m = f+1;
    G->degree = m;
    G->S[0] = 26; G->inS[26]=1;
    G->S[1] = 11; G->inS[11]=2;
    G->S[2] = 17; G->inS[17]=3;
    G->S[3] = 27; G->inS[27]=4;
    G->S[4] = 14; G->inS[14]=5;
    circ_graph_k(G);

    circ_graph_print(G);
    circ_graph_depth(G, UINT32_MAX, 0);
    
    printf("G=(%"PRIu32",[ ", n);
    for (i = 0; i < G->degree; i++) {
        printf("%"PRIu32" ", G->S[i]);
    }
    printf("]): W=%"PRIu32", D=%"PRIu32"(#%"PRIu32"), k=%"PRIu32", f=%"PRIu32"\n", 
        env.n*G->degree, G->attrs.DfU, G->attrs.lpc, G->attrs.k, G->attrs.f);
    //~ printf("Minimum improvement:");
    //~ for (j = 0; j < env.n; j++) {
        //~ printf(" %"PRIu32, G->improve[j]);
    //~ }
    //~ printf("\n");
    
    mutated_G = new_circ_graph();
    copy_circ_graph(G, mutated_G);
    mutate_circ_graph_2phase(mutated_G);
    circ_graph_k(mutated_G);
    if (mutated_G->attrs.k > f) {
        circ_graph_depth(mutated_G, UINT32_MAX, 0);
        
        printf("G=(%"PRIu32",[ ", n);
        for (i = 0; i < mutated_G->degree; i++) {
            printf("%"PRIu32" ", mutated_G->S[i]);
        }
        printf("]): W=%"PRIu32", D=%"PRIu32"(#%"PRIu32"), k=%"PRIu32", f=%"PRIu32"\n", 
            env.n*mutated_G->degree, mutated_G->attrs.DfU, mutated_G->attrs.lpc, 
            mutated_G->attrs.k, mutated_G->attrs.f);
        printf("Frequencies:");
        for (j = 0; j < mutated_G->degree; j++) {
            printf("%3"PRIu32" ", mutated_G->freq[j]);
        }
        printf("\n");
    }
    else {
        circ_graph_print(mutated_G);
        printf("   -> infeasible\n");
    }
    
    /* Destroy graph */
    destroy_circ_graph(&G);
    destroy_circ_graph(&mutated_G);
    
    fh_free_heap(&fh);
    
    /* Free environment */
    free_env();
    
    //~ fclose(depth_out);
    fclose(out);
    
    return 0;    
#endif

    /* Generate random circulant graph... */
    m = f+1;
    rand_circ_graph(G, m);    
    
    /* ...and evaluate it */
    circ_graph_k(G);
    circ_graph_depth(G, UINT32_MAX, 0);
    
    printf("G=(%"PRIu32",[ ", n);
    for (i = 0; i < G->degree; i++) {
        printf("%"PRIu32" ", G->S[i]);
    }
    printf("]): W=%"PRIu32", D=%"PRIu32"(#%"PRIu32"), k=%"PRIu32", f=%"PRIu32"\n", 
        env.n*G->degree, G->attrs.DfU, G->attrs.lpc, G->attrs.k, G->attrs.f);
        
#ifdef STORE_PATHS       
    printf("Paths:\n");
    uint32_t *st_paths;
    uint32_t path_idx, idx, end_idx, l, prefix_sum;
    char spaces[] = "                                                   ";
    for (i = 1; i < env.n; i++) {
        if (G->inS[i]) continue;
        print("(s=0, t=%d)\n", i);
        st_paths = G->paths + (i-1)*env.n;
        end_idx = 0;
        idx = 1;
        for (path_idx = 1; path_idx <= f+1; path_idx++) {
            /* Print path */
            print("path %2d: 0", path_idx);
            for (; idx < st_paths[end_idx]; idx++) {
                print("-%02d", st_paths[idx]);
            }
            print("-%02d\n", i);
            
            //~ /* Print matrix of possible offsets */
            //~ print("offsets:\n");
            //~ for (j = end_idx+1; j < st_paths[end_idx]; j++) {
                //~ print("%02d ", st_paths[j]);
            //~ }
            //~ print("%02d\n", i); 
            //~ for (j = end_idx+1; j < st_paths[end_idx]; j++) {
                //~ print("%.*s", 3*(j-(end_idx)),spaces);
                //~ for (l = j+1; l < st_paths[end_idx]; l++) {
                    //~ print("%02d ", (st_paths[l]-st_paths[j]+env.n)%env.n);
                //~ }
                //~ print("%02d\n", (i-st_paths[j]+env.n)%env.n);
            //~ }
            
            //~ for (j = 0; j <= st_paths[end_idx]; j++) {
                //~ for (l = j+1; l <= st_paths[end_idx]; l++) {
                    //~ print("+%02d", (st_paths[l]-st_paths[j]+env.n)%env.n);
                //~ } 
            //~ }
            
            //~ for (j = end_idx+1; j < st_paths[end_idx]; j++) {
                //~ print("%.*s", 3*(j-(end_idx))+13,spaces);
                //~ for (l = j+1; l < st_paths[end_idx]; l++) {
                    //~ print("+%02d", (st_paths[l]-st_paths[j]+env.n)%env.n);
                //~ }
                //~ print("+%02d\n", (i-st_paths[j]+env.n)%env.n);
            //~ }
            end_idx = idx++;
        }
        //~ break;
    }
#endif
 
#if 1
    printf("Frequencies:\n");
    for (j = 0; j < G->degree; j++) {
        printf("%3"PRIu32" ", G->freq[j]);
    }
    printf("\n");
#endif

#if 1
    printf("Improvements:\n");
    for (j = 0; j < env.n; j++) {
        printf("%3"PRIu32" ", G->improve[j]);
    }
    printf("\n");
#endif  

    mutated_G = new_circ_graph();
    copy_circ_graph(G, mutated_G);
    add_offset_rand(mutated_G);
    circ_graph_k(mutated_G);
    circ_graph_depth(mutated_G, UINT32_MAX, 0);
    
    printf("Add random offset: G=(%"PRIu32",[ ", n);
    for (i = 0; i < mutated_G->degree; i++) {
        printf("%"PRIu32" ", mutated_G->S[i]);
    }
    printf("]): W=%"PRIu32", D=%"PRIu32"(#%"PRIu32"), k=%"PRIu32", f=%"PRIu32"\n", 
            env.n*mutated_G->degree, mutated_G->attrs.DfU, mutated_G->attrs.lpc, 
            mutated_G->attrs.k, mutated_G->attrs.f);
        
    copy_circ_graph(G, mutated_G);
    add_offset_greedy(mutated_G);
    circ_graph_k(mutated_G);
    circ_graph_depth(mutated_G, UINT32_MAX, 0);
    
    printf("Add greedy offset: G=(%"PRIu32",[ ", n);
    for (i = 0; i < mutated_G->degree; i++) {
        printf("%"PRIu32" ", mutated_G->S[i]);
    }
    printf("]): W=%"PRIu32", D=%"PRIu32"(#%"PRIu32"), k=%"PRIu32", f=%"PRIu32"\n", 
            env.n*mutated_G->degree, mutated_G->attrs.DfU, mutated_G->attrs.lpc, 
            mutated_G->attrs.k, mutated_G->attrs.f);
    
#if 0    
    int mutate;
    for (mutate = 0; mutate < 3; mutate++) {
        mutate_circ_graph_greedy(G);
        W = env.n*G->degree;
        circ_graph_k(G);
        circ_graph_depth(G, UINT32_MAX, 0);
        printf("\nnew G=(%"PRIu32",[ ", n);
        for (i = 0; i < G->degree; i++) {
            printf("%"PRIu32" ", G->S[i]);
        }
        printf("]): W=%"PRIu32", D=%"PRIu32", k=%"PRIu32", f=%"PRIu32"\n", 
            env.n*G->degree, G->attrs.D, G->attrs.k, G->attrs.f);
        //~ for (i = 0; i < env.n; i++) {
            //~ printf("(%d,%d) ", i, G->inS[i]);
        //~ }
        //~ printf("\n");
    }
#endif
    
    /* Destroy graph */
    destroy_circ_graph(&G);
    destroy_circ_graph(&mutated_G);
#endif    
    /* Free heap */
    fh_free_heap(&fh);
    
    /* Free environment */
    free_env();
    
    //~ fclose(depth_out);
    fclose(out);
    
    return 0;
}

/**
 * Exhaustive search 
 * @return minimum depth 
 */
static uint32_t 
exhaustive_search( uint32_t m, 
                   uint32_t f, 
                   FILE* data, 
                   solution_t* solutions )
{
    circ_graph_t *G;
    solution_t *best_sol;
    uint32_t sol_count = 0, j;
    int ret;

    if (data)
        fprintf(data, "\n# Exhaustive search n=%d, m=%d, f=%d #\n", 
            env.n, m, f);
            
    best_sol = solutions;
    best_sol->D = env.n-1;
    best_sol->lp_count = 0;
    
    G = new_circ_graph();
    set_circ_graph_ft(G,f);
    while (next_circ_graph(G,m)) {
        /* Compute connectivity */
        circ_graph_k(G);
        //~ circ_graph_print(G);
        if (G->attrs.k <= f) {
            if (data) {
                fprintf(data, "G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
                for (j = 1; j < G->degree; j++) {
                    fprintf(data, ",%"PRIu32, G->S[j]);
                }
                fprintf(data, "]): infeasible k=%"PRIu32"\n", G->attrs.k);
            }
            continue;
        }
        /* Compute depth */
        ret = circ_graph_depth(G, best_sol->D, best_sol->lp_count);
        if (1 == ret) {
            continue;
        }
        solutions[++sol_count].D = G->attrs.DfU;
        solutions[sol_count].lp_count = G->attrs.lpc;
        if (data) {
            fprintf(data, "G=(%"PRIu32",[%"PRIu32, env.n, G->S[0]);
            for (j = 1; j < G->degree; j++) {
                fprintf(data, ",%"PRIu32, G->S[j]);
            }
            fprintf(data, "]):D=%"PRIu32"(#%"PRIu32"); k=%"PRIu32"\n", 
                    G->attrs.DfUfU, G->attrs.lpc, G->attrs.k);
        }
        
        if ( (G->attrs.DfU < best_sol->D) ||
             ((G->attrs.DfU == best_sol->D) && 
             (G->attrs.lpc < best_sol->lp_count)) )
        {
            /* Better solution; keep it */
            best_sol->D = G->attrs.DfU;
            best_sol->lp_count = G->attrs.lpc;
        }
    }
    destroy_circ_graph(&G);
    
    if (data) 
        fprintf(data, "D*=%"PRIu32"(#%"PRIu32")\n", best_sol->D, best_sol->lp_count);
    
    return sol_count;
}


static int 
test_fib_heap()
{
    fibonacci_heap_t fh;
    vertex_t v; v.idx = 13;
    
    fh_init_heap(&fh);
    
    v.d = 3;
    fh_insert(&fh, v);
    printf("insert %d: ", 3);
    fh_print_heap(&fh);
    
    v.d = 9;
    fh_insert(&fh, v);
    fh_print_heap(&fh);
    
    v.d = 1;
    fh_insert(&fh, v);
    printf("insert %d: ", 1);
    fh_print_heap(&fh);
    
    v.d = 2;
    fh_insert(&fh, v);
    printf("insert %d: ", 2);
    fh_print_heap(&fh);
    
    v = fh_extract_min(&fh);
    if (v.d != 1) return 1;
    printf("extract %d: ", v.d);
    fh_print_heap(&fh);
    
    v.d = 4;
    fh_insert(&fh, v);
    printf("insert %d: ", 4);
    fh_print_heap(&fh);
    
    v = fh_extract_min(&fh);
    if (v.d != 2) return 1;
    printf("extract %d: ", v.d);
    fh_print_heap(&fh);
       
    v = fh_extract_min(&fh);
    if (v.d != 2) return 1;
    printf("extract %d: ", v.d);
    fh_print_heap(&fh);

    //~ v.d = 1;
    //~ fh_insert(&fh, v);
    //~ if (fh_extract_min(&fh).d != 1) return 1;
    //~ if (fh_extract_min(&fh).d != 3) return 1;
    //~ if (fh_extract_min(&fh).d != 9) return 1;
    //~ if (fh_extract_min(&fh).d != UINT32_MAX) return 1;
    
    fh_free_heap(&fh);
    
    return 0;
}
#endif
