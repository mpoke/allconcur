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

 
#ifndef DA_MAXFLOW_H
#define DA_MAXFLOW_H

void da_cherkassky(digraph_t *G, uint32_t s, uint32_t t);
void da_clean();

#endif /* DA_MAXFLOW_H */
