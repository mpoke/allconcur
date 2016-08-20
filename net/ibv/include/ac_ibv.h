/**                                                                                                      
 * AllConcur
 * 
 * Network module -- IB Verbs
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef AC_IBV_H
#define AC_IBV_H

#include <ev.h>

void ac_ibv_reg_module(struct ev_loop *loop, 
                       void (*terminate)(int), 
                       int timer, 
                       void (*on_send_completed)());

#endif /* AC_IBV_H */
