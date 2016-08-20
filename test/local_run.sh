#!/bin/bash
#
# Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
#
# Author(s): Marius Poke <marius.poke@hlrs.de>
#

AC_PATH=$(cd `dirname "$0"` && pwd)/..
AC_CFG=${AC_PATH}/allconcur.cfg
AC=${AC_PATH}/bin/allconcur
TIMEOUT=1
HBPERIOD=0.01
WARMPERIOD=$((10*${TIMEOUT}))
SERVERFILE=${AC_PATH}/test/"allconcur.servers"
IPS=(`awk -F" " '{print $1}' $SERVERFILE`)
AC_PORTS=(`awk -F" " '{print $2}' $SERVERFILE`)
FD_PORTS=(`awk -F" " '{print $3}' $SERVERFILE`)
CLT_PORTS=(`awk -F" " '{print $4}' $SERVERFILE`)
SERVERCOUNT=${#IPS[@]}
RELIABILITY=6
REQSIZE=64
REQPERIOD="0.1 0.01"

make clean
make benchmark

mkdir -pm 755 ${AC_PATH}/run/local_run
cd ${AC_PATH}/run/local_run

# Create config files
for ((i=0; i<=${SERVERCOUNT}-1; ++i));
do
    # Generate config file
    LCL_CFG="allconcur$i.cfg"
    ACLOG="allconcur$i.log"
    FDLOG="allconcur$i.fd"
    T_ROUND="tround$i.data"
    T_REQUEST="trequest$i.data"
    THROUGHPUT="throughput$i.data"
    SELF="${IPS[$i]} ${AC_PORTS[$i]} ${FD_PORTS[$i]} ${CLT_PORTS[$i]}"
    cp ${AC_CFG} ${LCL_CFG}
    sed -e 's/#ACLOG#/'${ACLOG}'/g' \
        -e 's/#FDLOG#/'${FDLOG}'/g' \
        -e 's/#T_ROUND#/'${T_ROUND}'/g' \
        -e 's/#T_REQUEST#/'${T_REQUEST}'/g' \
        -e 's/#THROUGHPUT#/'${THROUGHPUT}'/g' \
        -e 's|#REQPERIOD#|'"${REQPERIOD}"'|g' \
        -e 's/#REQSIZE#/'${REQSIZE}'/g' \
        -e 's|#SERVERFILE#|'"${SERVERFILE}"'|g' \
        -e 's|#SELF#|'"${SELF}"'|g' \
        -e 's/#TIMEOUT#/'${TIMEOUT}'/g' \
        -e 's/#CHECKFAIL#/'${CHECKFAIL}'/g' \
        -e 's/#HBPERIOD#/'${HBPERIOD}'/g' \
        -e 's/#WARMPERIOD#/'${WARMPERIOD}'/g' \
        ${LCL_CFG} > sed.out && mv sed.out ${LCL_CFG} || exit 1    
done


# Start servers
for ((i=0; i<=${SERVERCOUNT}-1; ++i));
do
    LCL_CFG="allconcur$i.cfg"
    OUT="allconcur$i.out"
    echo "Executing: ${AC} -n ${SERVERCOUNT} -r ${RELIABILITY} -c ${LCL_CFG} --timer --latency --tcp &"
    # valgrind --log-file=${OUT} --leak-check=full --track-origins=yes 
    ${AC} -n ${SERVERCOUNT} -r ${RELIABILITY} -c ${LCL_CFG} --timer --tcp &
    ap_pids[$i]=$!
    echo ${ap_pids[$i]}
done

# Stop servers
for ((i=0; i<=${SERVERCOUNT}-1; ++i));
do
    while kill -0 ${ap_pids[$i]} >/dev/null 2>&1
    do
        sleep 0.1
    done
    kill -n SIGINT ${ap_pids[$i]}
    LCL_CFG="allconcur$i.cfg"
    rm ${LCL_CFG}
done
