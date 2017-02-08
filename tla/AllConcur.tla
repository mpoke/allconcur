(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE AllConcur ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, Graphs, ExactSeqs

LOCAL INSTANCE TLC

CONSTANTS n,        \* number of servers
          f,        \* fault tolerance 
          GEdges,    \* set of edges for overlay network (p,q) \in GEdges iif p -> q
          emptyMessage \* EmptyMessage[p] a flag indicating whether p has a message to send 
          
(*
 * M[pi] contains the set of pi's know messages
 * F[pi][pj] contains the set of pj's successors from which pi received notifications of pj's failure
 * g[pi][pj] contains pi's tracking digraph for pj's message 
 *      if pi=pj, V(g[pi][pj]) = {}; else V(g[pi][pj]) = q
 * flag[pi].nonFaulty flag indicating whether pi is nonfaulty
 *         .abcast flag indicating whether pi A-broadcast its message
 *         .done flag indicating whether pi terminated
 * FD[pk][pj] flag indicating whether pk detected pj's failure
 *)
VARIABLES M, 
          F,
          g,
          flag,
          FD,
          sendBuf, recvBuf, recvMsg, \* internal variable for networking
          final_state      

\* ASSUMPTION: n > 1
ASSUME ServerCountNat == (n \in Nat) /\ (n > 1)

Server == \* server identifiers 
    (0 .. n-1)
    
ASSUME IsFiniteSet(Server)    

G == \* the overlay network
    [node |-> Server, edge |-> GEdges]
    
\* ASSUMPTION: G is a regular digraph with degree larger than the fault tolerance
ASSUME IsDirectedGraph(G) /\ IsGraphRegular(G) /\ GraphDegree(G) > f
\* ASSUMPTION: The overlay network G is a digraph with connectivity > f
\* ASSUME IsDirectedGraph(G) /\ IsGraphFaultTolerant(G,f)  
    
Message ==  \* possible messages exchanged between servers 
    [type : {"BCAST"}, owner : Server] 
    \cup {fail \in [type : {"FAIL"}, owner : Server, target : Server]: fail.owner # fail.target} 
    
ASSUME MessageSetNotEmpty == Message # {}    

INSTANCE Networking  

INSTANCE TrackingDigraph        

(* 
EmptyMessage == \* EmptyMessage[i] a flag indicating whether pi has a message to send 
    CHOOSE BitArray \in [Server -> {0,1}] : \E p \in Server : BitArray[p] = 1
*)

\* ASSUMPTION: At least one server has a message to A-broadcast    
ASSUME emptyMessage \in [Server -> {0,1}] /\ \E p \in Server : emptyMessage[p] = 0

-----------------------------------------------------------------------------

(*(* 
 * Fast source (Source: Leslie Lamport, Specifying Systems: 
 *  The TLA+ Language and Tools for Hardware and Software Engineers, 2002
 *)
FastSort(S) == 
    LET MakeSeq[SS \in SUBSET S] == 
            IF SS = {} THEN << >>
                       ELSE LET ss == CHOOSE ss \in SS : TRUE
                            IN Append(MakeSeq[SS\{ss}],ss)
    IN SortSeq(MakeSeq[S], <) 
 *)       
-----------------------------------------------------------------------------

Init == \* The initial predicate
    /\ NetInit
    /\ M = [p \in Server |-> {}]
    /\ F = [p \in Server |-> [q \in Server |-> {} ]]        
    /\ g = [p \in Server |-> [q \in Server |-> [node |-> {q}, edge |-> {}] ]]
    /\ flag = [nonFaulty |-> [p \in Server |-> 1],
               abcast |-> [p \in Server |-> 0],
               done |-> [p \in Server |-> 0]]
    /\ FD = [pk \in Server |-> [pj \in Server |-> 0]]
    /\ final_state = 0

TypeInvariant == \* The type invariant
    /\ NetTypeInvariant
    /\ M \in [Server -> SUBSET Server] 
    /\ F \in [Server -> [Server -> SUBSET Server]]
    /\ g \in [Server -> [Server -> DigraphType(Server)]]
    /\ flag \in [nonFaulty : [Server -> {0, 1}], 
                 abcast : [Server -> {0, 1}],
                 done : [Server -> {0, 1}]]
    /\ FD \in [Server -> [Server -> {0, 1}]]
    /\ final_state \in {0, 1}
               
-----------------------------------------------------------------------------

Abcast(p) == \* A-broadcast own message (message not empty)
    \* enabled only if...
    /\ flag.done[p] = 0 \* ...not done
    /\ flag.nonFaulty[p] = 1 \* ...not failed
    /\ sendBuf[p] = << >> \* ...not sending
    /\ flag.abcast[p] = 0 \* ...message not already a-bcast
    /\ emptyMessage[p] = 0 \* ...message not empty
    /\ Debug([op |-> "Abcast", args |-> <<p>>])
    \* send own message 
    /\ SendMessage(p, <<[type |-> "BCAST", owner |-> p]>>, flag.nonFaulty)
    /\ M' = [M EXCEPT ![p] = M[p] \cup {p}]
    /\ flag' = [flag EXCEPT !.abcast[p] = 1]
    /\ g' = [g EXCEPT ![p][p] = [node |-> {}, edge |-> {}]]
    /\ UNCHANGED <<F, FD, recvBuf, recvMsg, final_state>>
    
TXMessage(p) ==
    \* enabled only if...
    /\ flag.done[p] = 0 \* ...not done
    /\ flag.nonFaulty[p] = 1 \* ...not failed
    \* transmit next message
    /\ NetTXMessage(p)
    /\ UNCHANGED <<M, F, g, flag, FD, recvMsg, final_state>>
    
ReceiveBCAST(p, m) ==
    /\ IF /\ flag.abcast[m.owner] = 1 \* m was A-broadcasted by it's owner
          /\ m.owner \notin M[p] \* first time receiving m
        THEN IF flag.abcast[p] = 0 \* onw message not A-broadcast
            THEN /\ SendMessage(p, <<[type |-> "BCAST", owner |-> p], m>>, flag.nonFaulty) \* send both messages further
                 /\ M' = [M EXCEPT ![p] = M[p] \cup {p, m.owner}]
                 /\ g' = [g EXCEPT ![p][p] = [node |-> {}, edge |-> {}], 
                                   ![p][m.owner] = [node |-> {}, edge |-> {}]]
                 /\ flag' = [flag EXCEPT !.abcast[p] = 1]
            ELSE /\ SendMessage(p, <<m>>, flag.nonFaulty) \* send only m further
                 /\ M' = [M EXCEPT ![p] = M[p] \cup {m.owner}]
                 /\ g' = [g EXCEPT ![p][m.owner] = [node |-> {}, edge |-> {}]]
                 /\ UNCHANGED <<flag>>
        ELSE (* Either m was already received, hence ignore it, or it was never A-broadcast. 
                The later is impossible, but it makes it much easier to prove integrity. *)
             UNCHANGED <<M, g, flag, sendBuf>>

ReceiveFAIL(pi, m) ==  
    IF m.owner \notin F[pi][m.target] 
        THEN \* new failure notification
             /\ SendMessage(pi, <<m>>, flag.nonFaulty) \* send it further           
             /\ F' = [F EXCEPT ![pi][m.target] = F[pi][m.target] \cup {m.owner}]
             \* update every tracking digraph that contains m.target
             /\ LET pj == m.target
                    pk == m.owner
                    DiscSrv(p_star, tg) == \* Set of nodes that cannot be reached from a node p in a digraph tg 
                        {q \in tg.node : ~AreConnected(p_star, q, tg)}
                        \*{q \in tg.node : ~AreConnectedTLAPS(p_star, q, tg)} 
                    (* Prune tracking digraph: remove disconnected nodes and the corresponding edges*)
                    PruneDisc(p_star, tg) ==
                        AdjustEdgeInDigraph([tg EXCEPT !.node = tg.node \ DiscSrv(p_star, tg)])
                    (* Prune tracking digraph: destroy digraph if all servers are faulty *)
                    PruneAllFaulty(p_star, tg) ==
                        IF \A q \in tg.node : F[pi][q] # {} THEN [node |-> {}, edge |-> {}] ELSE tg
                IN (* Update pi's tracking digraphs *)  
                   /\ g' = [g EXCEPT ![pi] = [p_star \in Server |-> 
                                (* If the failed server not in the tracking digraph, then leave unchanged *)
                                IF pj \notin g[pi][p_star].node THEN g[pi][p_star] 
                                (* Otherwise, update the digraph and then check whether all servers are know to have failed *)
                                (* \* !!! COMMENT FOR TLAPS 
                                ELSE LET new_tg ==                        
                                        (* If the failed server already has successors in the tracking digraph, it means 
                                           pi already received a notification of pj's failure. *)        
                                        IF Successors(g[pi][p_star], pj) # {} 
                                        (* pk cannot be suspected to have received directly from pj p_star's message;
                                           hence, remove the edge <<pj, pk>> (if there is one).
                                           Note that the removal of an edge may disconnect nodes from the root; disconnected servers 
                                           must be removed. *)
                                        THEN IF <<pj,pk>> \in g[pi][p_star].edge  
                                                THEN PruneDisc(p_star, [g[pi][p_star] EXCEPT !.edge = g[pi][p_star].edge \ {<<pj, pk>>}])
                                                ELSE g[pi][p_star]
                                        (* Otherwise, extends the tracking digraph by adding pj's successors, the successors of 
                                           any faulty successor, and so on.  *) 
                                         ELSE UpdateTrackingDigraph(pi, pj, pk, p_star, g[pi][p_star])]]         
                                     IN PruneAllFaulty(p_star, new_tg)]]
                                *)     
                                (* In case of TLAPS, just reconstruct the tracking digraph from scratch and then prune it if all 
                                   servers are faulty; note that TrackingDigraph() covers all of the above cases. 
                                   Also, note that we reconstruct the tracking digraph using the new failure notification, hence, 
                                   the primed call. *)
                                \* !!! COMMENT FOR TLC model  
                                ELSE PruneAllFaulty(p_star, TrackingDigraph(pi, p_star))']]
                                
                   \*/\ Debug(g')
    ELSE UNCHANGED <<F, g, sendBuf>> 
   
ReceiveMessage(p) ==
    \* enabled only if...
    /\ flag.done[p] = 0 \* ...not done
    /\ flag.nonFaulty[p] = 1 \* ...not failed
    /\ sendBuf[p] = << >> \* ...not sending
    \* deliver next message from recvBuf (if there is any) and store it in recvMsg
    /\ DeliverMessage(p)
    /\ Debug([op |-> "ReceiveMessage", args |-> <<p, recvMsg'>>])
    /\ CASE recvMsg'.type = "BCAST" -> 
                    /\ ReceiveBCAST(p, recvMsg')
                    /\ UNCHANGED <<F, FD, final_state>>
          [] recvMsg'.type = "FAIL" ->
                    /\ ReceiveFAIL(p, recvMsg')
                    /\ UNCHANGED <<M, flag, FD, final_state>> 
          [] OTHER -> UNCHANGED <<M, F, g, flag, FD, sendBuf, final_state>>                         
          
Adeliver(p) ==
    \* enabled only if...
    /\ flag.done[p] = 0 \* ...not done
    /\ flag.nonFaulty[p] = 1 \* ...not failed
    /\ sendBuf[p] = << >> \* ...not sending
    /\ (\A q \in Server : g[p][q].node = {}) \* all tracking digraphs are empty
    /\ Debug([op |-> "Adeliver", args |-> <<p>>])
    \* mark p as done
    /\ flag' = [flag EXCEPT !.done[p] = 1]
    /\ UNCHANGED <<M, F, g, FD, sendBuf, recvBuf, recvMsg, final_state>>
    
Fail(p) ==
    \* enabled only if... 
    /\ flag.nonFaulty[p] = 1 \* ...not failed
    /\ Cardinality({q \in Server : flag.nonFaulty[q] = 0}) < f \* ...less than f server failed
    /\ Debug([op |-> "Fail", args |-> <<p>>])
    \* mark p as failed
    /\ flag' = [flag EXCEPT !.nonFaulty[p] = 0]
    /\ UNCHANGED <<M, F, g, FD, sendBuf, recvBuf, recvMsg, final_state>>
    
DetectFailure(pj,pk) == \* Server pk detects pj's failure
    \* enabled only if...
    /\ flag.nonFaulty[pj] = 0 \* ...pj failed 
                             \* note that this condition entails a perfect FD
    /\ flag.nonFaulty[pk] = 1 \* ...pk didn't fail
    /\ pk \in Successors(G,pj) \* ...pk is a successor of pj in G
    /\ FD[pk][pj] = 0 \* ...pk did not already detect pj's failure
    /\ Debug([op |-> "DetectFailure", args |-> <<pj, pk>>, failed |-> pj])
    \* add FAIL message to pk's receive buffer
    \* !!! note that we cannot directly handle the FAIL message; if mj were in the receive buffer, 
    \* the assumption that a <FAIL, pj, pk> message indicates that pk did not receive mj is false
    /\ recvBuf' = [recvBuf EXCEPT ![pk] = Append(recvBuf[pk], [type |-> "FAIL", owner |-> pk, target |-> pj])]
    /\ FD' = [FD EXCEPT ![pk][pj] = 1] 
    /\ UNCHANGED <<M, F, g, flag, sendBuf, recvMsg, final_state>>

PrintFinalState == \* print the final state
    \* enabled only if...
    /\ final_state = 0 \* ...not already printed
    /\ \A p \in Server: flag.nonFaulty[p] = 1 => flag.done[p] = 1 \* ...each non-faulty server terminated
    /\ final_state' = 1
    /\ Info("AllConcur terminated")
    /\ Info([flag |-> flag, M |-> M])
    /\ Debug([F |-> F, g |-> g, FD |-> FD, sendBuf |->sendBuf, recvBuf |-> recvBuf, recvMsg |-> recvMsg]) 
    /\ UNCHANGED <<M, F, g, flag, FD, sendBuf, recvBuf, recvMsg>>  
    /\ Info("#########################################")

Next == 
    \/ \E p \in Server : \/ Abcast(p)  \* A-broadcast p's message 
                         \/ TXMessage(p)    \* transmit one of p's messages
                         \/ ReceiveMessage(p) \* receive a message
                         \/ Adeliver(p)    \* terminate
                         \/ Fail(p)
                         \/ (\E q \in Server : DetectFailure(p,q)) \* q detects p's failure
   \*\/ PrintFinalState

vars == <<M, F, g, flag, FD, sendBuf, recvBuf, recvMsg, final_state>>
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

(***************************************************************************
 * Safety Properties
 *
 * (Integrity) For any message m, every non-faulty server A-delivers m at 
 * most once, and only if m was previously A-broadcast by sender(m). 
 *
 * (Total order) If two non-faulty servers p and q A-deliver messages 
 * m1 and m2, then p A-delivers m1 before m2 , if and only if q A-delivers 
 * m1 before m2.
 * !!! Note: since p A-delivered messages in M[p] in a deterministic order, 
 * we replace total order with set agreement 
 * (Set agreement) Let p and q be any two non-faulty servers. Then, after 
 * termination, M[p] = M[q].
 *
 * (FD Accuracy) No server is suspected to have failed before actually 
 * failing
 * 
 * (TD Invariant) Any tracking digraph must have the four properties
 ***************************************************************************)
Integrity == \* PROPERTY: Integrity
    \A p \in Server : (flag.nonFaulty[p] = 1 => (\A m \in M[p] : flag.abcast[m] = 1))
    \* Note that "a server A-delivers m at most once" is ensured by constuction (M[p] is a set)     
                                                   
SetAgreement == \* PROPERTY: SetAgreement => Total order
    \A p,q \in Server : ( /\ (flag.nonFaulty[p] = 1 /\ flag.done[p] = 1)
                          /\ (flag.nonFaulty[q] = 1 /\ flag.done[q] = 1) ) => M[p] = M[q]
                          
MaximumFailure == \* PROPERTY: Maximum f failures
    Cardinality({q \in Server : flag.nonFaulty[q] = 0}) \leq f
    
FDAccuracy == \* PROPERTY: FD Accuracy
    \A p \in Server : flag.nonFaulty[p] = 1 => (\A q \in Server : FD[q][p] = 0)   
    
TDInvariant ==
    \A p,q \in Server :  
        /\ TDHasRoot(g[p][q], q) 
        /\ TDFaultyNodeInvariant(g[p][q], p)
        /\ TDNodeInvariant(g[p][q], p, q) 
        /\ TDEdgeInvariant(g[p][q], p)
    
-----------------------------------------------------------------------------

(***************************************************************************
 * Liveness Properties
 *
 * (Validity) If a non-faulty server A-broadcasts m, then it eventually 
 * A-delivers m. 
 *
 * (Agreement) If a non-faulty server A-delivers m, then all non-faulty 
 * servers eventually R-deliver m.
 *
 * (FD Completeness) All failures are eventually detected
 * 
 * (FD Eventual Accuracy) No server is suspected to have failed before actually 
 * failing  
 ***************************************************************************)
 (* A message m is A-delivered by a server p if m is in 
    p's set of known messages when it terminates *)
a_deliver(p, m) == \* p A-delivers m 
    /\ m \in M[p]
    /\ flag.done[p] = 1 
 
Validity == \* PROPERTY: Validity
    \* whenever a server p is ALWAYS non-faulty and A-broadcast a message m, 
    \* EVENTUALLY p A-delivers m (i.e., it knows about m and it terminates)
    \A p \in Server : ([](flag.nonFaulty[p] = 1) /\ flag.abcast[p] = 1) ~> a_deliver(p, p)      
                                                   
Agreement == \* PROPERTY: Agreement
    \* whenever a server p is ALWAYS non-faulty and A-delivered a message m, 
    \* EVENTUALLY, every other non-faulty server q A-delivers m. 
    \A p \in Server, m \in Server : ([](flag.nonFaulty[p] = 1) /\ a_deliver(p, m)) ~> 
                (\A q \in Server : flag.nonFaulty[q] = 1 => a_deliver(q, m))
                
FDCompleteness == \* PROPERTY: FD Completeness
    \* whenever a server p fails, EVENTUALLY every non-faulty successors of p detects p's failure
    \A p \in Server : flag.nonFaulty[p] = 0 ~> (\A q \in Successors(G, p) : flag.nonFaulty[q] = 1 => FD[q][p] = 1)

LiveSpec == Spec /\ WF_vars(Next) 

=============================================================================