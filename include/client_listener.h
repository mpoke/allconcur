/**                                                                                                      
 * AllConcur 
 * 
 * Client listener
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef CLIENT_LISTENER_H
#define CLIENT_LISTENER_H

#include <ac_ep.h>

void *wait_for_clients();
int cl_add_reply(uint32_t in, shared_buf_t *sh_buf);

#endif /* CLIENT_LISTENER_H */
