/**                                                                                                      
 * AllConcur
 * 
 * Network module -- TCP
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef AC_TCP_H
#define AC_TCP_H

#include <ev.h>

void ac_tcp_reg_module(struct ev_loop *loop, 
                       void (*terminate)(int), 
                       int timer, 
                       void (*on_send_completed)());

#endif /* AC_TCP_H */
