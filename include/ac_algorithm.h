/**                                                                                                      
 * AllConcur
 * 
 * The algorithm
 * 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */
 
#ifndef AC_ALGORITHM_H
#define AC_ALGORITHM_H

#define SRV_INIT        0
#define SRV_CONNECTED   (1 << 0)
#define SRV_GOT_MSG     (1 << 1)
#define SRV_FAILED      (1 << 2)
#define SRV_INPUT       (1 << 4)
#define SRV_MSG_LOST    (1 << 5)

#define MSG_INPUT 1
#define MSG_FAIL  2
#define MSG_MTU   3

void handle_prev_data(void *endpoint, void *recv_buf, uint32_t recv_len);
void handle_next_data(void *endpoint, void *recv_buf, uint32_t recv_len);
void* new_predecessor(void *conn);
void* new_successor(void *conn);
void check_termination();
void poll_fd();
void poll_request_pool();

int server_is_failed(uint32_t sid);
int server_failed_crt_round(uint32_t sid);

#ifdef BENCHMARK 
void benchmark_init();
void benchmark_destroy();
#endif



#endif /* AC_ALGORITHM_H */
