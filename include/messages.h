/**                                                                                                      
 * AllConcur
 * 
 * Message queue (for pending and premature messages)
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef MESSAGES_H
#define MESSAGES_H

#include <ac_ep.h>

/* Message handler */
typedef void (*message_handler_t)(message_t *msg, uint32_t from_sid);

extern message_queue_t *premature_msgs;

message_queue_t* add_message(message_queue_t **mq_ptr, 
                             message_t *msg, 
                             uint32_t from_sid);
void destroy_message_queue(message_queue_t **mq_ptr);
int send_pending_messages(ep_t *ep);
int handle_premature_messages(message_queue_t **mq_ptr, 
                              uint64_t sqn,
                              message_handler_t mh);

#endif /* MESSAGES_H */
