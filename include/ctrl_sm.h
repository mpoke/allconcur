/**                                                                                                      
 * AllConcur
 * 
 * Control state machine
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef CTRL_SM_H
#define CTRL_SM_H

#include <kvs_ht.h>
#include <ac_types.h>

kvs_ht_t* new_ctrl_sm();
uint64_t add_server_to_ctrl_sm(kvs_ht_t *ctrl_sm, srv_value_t *server);
int remap_vertexes_to_servers(kvs_ht_t *ctrl_sm, 
                              srv_t *map, 
                              uint32_t n);
                              
uint64_t add_client_to_ctrl_sm(kvs_ht_t *ctrl_sm, cid_t *cid);
uint64_t get_expected_sqn(kvs_ht_t *ctrl_sm, cid_t *cid);
int update_expected_sqn(kvs_ht_t *ctrl_sm, cid_t *cid, uint64_t sqn);


#endif /* CTRL_SM_H */
