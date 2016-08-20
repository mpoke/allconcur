/**                                                                                                      
 * AllConcur 
 * 
 * Initialization
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef AC_INIT_H
#define AC_INIT_H

int ac_init(uint32_t n, uint32_t rnines);
int update_digraph(uint32_t n, uint32_t rnines);
void ac_destroy();

#endif /* AC_INIT_H */

