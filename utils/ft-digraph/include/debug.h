/**          
 * Fault tolerant digraphs
 *                                                                                             
 * Debugging and logging utilities
 *
 * Copyright (c) 2015 HLRS, University of Stuttgart. 
 *               All rights reserved.
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

#endif /* DEBUG_H */
