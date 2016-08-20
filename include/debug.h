/**          
 * AllConcur
 *                                                                                             
 * Debugging and logging utilities
 *
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Copyright (c) 2014-2015 ETH-Zurich. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 */

#ifndef DEBUG_H
#define DEBUG_H

#include <stdio.h>
#include <errno.h>
#define __STDC_FORMAT_MACROS
#include <inttypes.h>
#include <sys/time.h>
#include <string.h>
#include <assert.h>

extern FILE *dbg_stream;
extern FILE *fd_stream;

//#ifdef INFO
#define info(fmt, ...) do {\
    fprintf(dbg_stream, fmt, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)

#define info_wtime(fmt, ...) do {\
    struct timeval _debug_tv;\
    gettimeofday(&_debug_tv,NULL);\
    fprintf(dbg_stream, "[%lu:%06lu] " fmt, _debug_tv.tv_sec, _debug_tv.tv_usec, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)
//#else
//#define info(fmt, ...)
//#define info_wtime(fmt, ...)
//#endif

#define IMHERE info("%s/%d/%s()\n", __FILE__, __LINE__, __func__);

#define error(fmt, ...) do {\
    fprintf(dbg_stream, "[ERROR] %s/%d/%s(): " fmt, __FILE__, __LINE__, __func__, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)

#if 1
#define fd_info(fmt, ...) do {\
    fprintf(fd_stream, fmt, ##__VA_ARGS__); \
    fflush(fd_stream); \
} while(0)

#define fd_info_wtime(fmt, ...) do {\
    struct timeval _debug_tv;\
    gettimeofday(&_debug_tv,NULL);\
    fprintf(fd_stream, "[%lu:%06lu] " fmt, _debug_tv.tv_sec, _debug_tv.tv_usec, ##__VA_ARGS__); \
    fflush(fd_stream); \
} while(0)
#else
#define fd_info(fmt, ...) 
#define fd_info_wtime(fmt, ...) 
#endif

#define fd_error(fmt, ...) do {\
    fprintf(fd_stream, "[ERROR] %s/%d/%s(): " fmt, __FILE__, __LINE__, __func__, ##__VA_ARGS__); \
    fflush(fd_stream); \
} while(0)


#define VERB_ERR(verb, ret) \
    error("%s returned %d errno %d (%s)\n", verb, ret, errno, strerror(errno))

#ifdef DEBUG
#define debug(fmt, ...) do {\
    fprintf(dbg_stream, "[DEBUG] %s/%d/%s() " fmt, __FILE__, __LINE__, __func__, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)
#define print(fmt, ...) do {\
    fprintf(dbg_stream, fmt, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)
#define print_cnd(condition, fmt, ...) if (condition) { \
    fprintf(dbg_stream, fmt, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} 
#define print_wtime(fmt, ...) do {\
    struct timeval _debug_tv;\
    gettimeofday(&_debug_tv,NULL);\
    fprintf(dbg_stream, "[%lu:%lu] " fmt, _debug_tv.tv_sec, _debug_tv.tv_usec, ##__VA_ARGS__); \
    fflush(dbg_stream); \
} while(0)
#else
#define debug(fmt, ...)
#define print(fmt, ...)
#define print_cnd(condition, fmt, ...)
#define print_wtime(fmt, ...)
#endif

#ifdef DEBUG
static inline void 
dump_bytes(void *addr, uint32_t len, char *header) {
    uint32_t i, count;
    uint8_t *bytes = (uint8_t*)addr, last_byte;
    info("### %s: [" , header);
    if (!len) {
        info("]\n");
        return;
    }
    last_byte = bytes[0];
    count = 1;
    for (i = 1; i < (uint32_t)(len); i++) {
        if (bytes[i] == last_byte) {
            count++;
        }
        else { 
            if (count > 1) {
                info("%"PRIu8"[%"PRIu32"], ", last_byte, count);
            }
            else {
                info("%"PRIu8", ", last_byte);
            }
            count = 1;
            last_byte = bytes[i];
        }
    }
    if (count > 1) {
        info("%"PRIu8"[%"PRIu32"], ", last_byte, count);
    }
    else {
        info("%"PRIu8", ", last_byte);
    }
    info("]\n");
}
#else
static inline void 
dump_bytes(void *addr, uint32_t len, char *header) {}
#endif

#endif /* DEBUG_H */
