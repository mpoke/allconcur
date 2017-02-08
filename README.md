# AllConcur 
## Algorithm for LeaderLess CONCURrent atomic broadcast

#### Brief 
An implementation of the AllConcur algorithm over both TCP/IP and InfiniBand Verbs [1].

#### Building benchmarks

###### Prerequisites
- libev (version >= 4.15)  
- gmplib (version >= 6.1.0)  
- mpfrlib (version >= 3.1.3)  

###### Generate Makefile
```
./configure --help
usage  : $0 [options]  
options: [--prefix=DIR]                # Installation directory  
         [--with-ev=DIR]               # ev installation directory  
         [--with-mpfr=DIR]             # mpfr installation directory  
         [--with-gmp=DIR]              # gmp installation directory  
         [--enable-ibv]                # enable IBV network module  
         [--with-ibv=DIR]              # IB verbs installation directory  
         [--with-rdmacm=DIR]           # RDMA-CM installation directory  
```         
###### Build
```  
make benchmark
```  

#### Running benchmarks
###### Directly start an AllConcur server
```  
$ ./bin/allconcur -h
Usage: ./bin/allconcur [OPTIONS]
OPTIONS:
	-c <config-file>         configuration file
	[--tcp | --ibv]          server-interconnection type (dafault=ibv)
	[-n <size>]              number of nodes (default=6)
	[-r <k-nines>]           required reliability (default=6)
	[--join]                 join group a servers
	   -s <hostname>         [join] server's hostname
	   -p <port>             [join] server's port
	[--timer]                get runtime estimates (default no)
	[--latency]              run latency benchmark
	[--throughput]           run peak throughput benchmark
	[--failure]              run failure benchmark
```  
By default, each AllConcur server periodically generates requests; check the config file (e.g., allconcur.cfg) for the request size (i.e., req_size) 
and the request generating period (i.e., req_period). 
Other benchmarks:
- latency -- only one server A-broadcast a single request;
- throughput -- each server batches more requests in a single message, 
which is then A-broadcast; max_batching (see config file) gives the maximum 
batching factor;
- failure -- fault-tolerant agreement.

###### Start an AllConcur server through MPI
The benchmarks can be started also through the following MPI launcher (this automatically creates the configuration file):
``` 
$ ./bin/allconcur_launcher -h
Usage: ./bin/allconcur_launcher [OPTIONS]
OPTIONS:
	-n <size>                    number of nodes
	[--tcp | --ibv]              server-interconnection type (default=ibv)
	[-r <k-nines>]               required reliability (default=6)
	[-p <port>]                  inter-server port (default=55000)
	[-s <size>]                  request size in bytes (default=64)
	[--timer]                    timer
	[--treq]                     run request rate benchmark
	[--ctreq]                    run constant request rate benchmark
	   [-P <req_period>]         [treq|ctreq] period of generating request in ms (default=1)
	[--latency]                  run latency benchmark
	[--throughput]               run peak throughput benchmark (default)
	   [-b <batching factor>]    [throughput] max batching factor (default=512)
	[--failure]                  run failure benchmark
``` 
e.g., the following command starts the throughput benchmark
``` 
mpirun -np 8 ./bin/allconcur_launcher -n 8 -s 1024 --throughput -b 512
``` 

#### Folder overview
- ./bin -- binaries
- ./lib -- libraries
- ./src -- source files
    - allconcur.c -- main function
    - ac_init.c -- initialization
    - ac_algorithm.c -- the AllConcur algorithm
    - ac_fd.c -- failure detector
    - messages.c -- message queue (for pending and premature messages)
    - request_pool.c -- request pool (circular buffer)
    - g_array.c -- tracking digraphs
    - kvs_ht.c -- key-value store (hash-table)
    - ctrl_sm.c -- control state machine (for consistency of control data)
    - client_listener.c -- listening for incoming client requests 
- ./include -- header files
- ./loggp -- code for computing LogGP params (based on Netgauge [2])
- ./net -- network module
    - ibv -- InfiniBand verbs
    - tcp -- TCP sockets
- ./test -- scripts 
- ./utils
    - ft-digraph -- fault tolerant digraph library
    - rbtree -- red-black Trees implementation (Linux)
- ./tla -- TLA+[3] specifcation and proofs 


#### Avoid 200ms delay on TCP ([reduce TCP RTO on Linux] (http://unix.stackexchange.com/questions/210367/changing-the-tcp-rto-value-in-linux))
By default, the min RTO on Linux is ~200ms. To see the RTO values for open TCP connections use the following command:
``` 
ss -i
``` 
The RTO can be changed only per route; e.g.,
``` 
$ ip route
10.0.2.0/24 dev eth0  proto kernel  scope link  src 10.0.2.15 
169.254.0.0/16 dev eth0  scope link  metric 1002 
default via 10.0.2.2 dev eth0
$ ip route change default via 10.0.2.2 dev eth0 rto_min 5ms
$ ip route
10.0.2.0/24 dev eth0  proto kernel  scope link  src 10.0.2.15 
169.254.0.0/16 dev eth0  scope link  metric 1002 
default via 10.0.2.2 dev eth0  rto_min lock 5ms
``` 

#### References
[1] M. Poke, T. Hoefler, and C. W. Glass: *Allconcur: Leaderless concurrent atomic broadcast (extended version)*, CoRR, abs/1608.05866, 2016.

[2] T. Hoefler, A. Lichei and W. Rehm: *Low-Overhead LogGP Parameter Assessment for Modern Interconnection Networks*, IEEE IPDPS 2007 

[3] L. Lamport: *Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers*, Addison-Wesley Longman Publishing Co., Inc., Boston, MA, USA, 2002
