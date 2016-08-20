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

#ifndef SSP_H
#define SSP_H


void ssp(digraph_t *G, uint32_t s, uint32_t t);
uint32_t largest_shorthest_path(digraph_t* G, uint32_t root);
void ssp_clean();

#endif /* SSP_H */
