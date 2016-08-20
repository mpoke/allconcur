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
 
#ifndef OPT_H
#define OPT_H

#define __STDC_FORMAT_MACROS
#include <inttypes.h>

#define OPT_EXAUST 	0
#define OPT_RAND 	1
#define OPT_HILL 	2
#define OPT_CMP_RAND_HILL 3

struct obj_func_t {
	uint32_t D;			/* diameter */
    uint32_t DfU;       /* upper bound for the fault diameter */
    uint32_t DfL;       /* lower bound for the fault diameter */
    uint32_t lpc;	/* longest path count */
};
typedef struct obj_func_t obj_func_t;

static const uint32_t sample_count = 10000000;
static const uint32_t max_same_sol_count = 20;
static const uint32_t mc_repeat = 1;

void free_opt_env();
void optimize( uint32_t n, 
               uint32_t degree, 
               uint32_t f, 
               obj_func_t ub, 
               int opt_type );

#endif /* OPT_H */
