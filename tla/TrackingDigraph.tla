(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE TrackingDigraph ----------------------
(***************************************************************************
 * Tracking digraphs: digraphs used to track the whereabouts of messages 
 ***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Graphs, ExactSeqs

CONSTANTS Server, \* set of servers
          G,      \* overlay network
          F,      \* set of known failures
          M,      \* set of known messages
          g       \* set of tracking digraphs 

AXIOM GnodesSrv == G.node = Server
-----------------------------------------------------------------------------

(* 
   Operator used by TLC to update the tracking digraphs; due to the recursive 
   nature, it's not suitable for TLAPS. 
   
   Update pi's suspicion of who has p_star's message as a result of receiving 
   pk's notification of pj's failure. 
*)      
UpdateTrackingDigraph(pi, pj, pk, p_star, gi_pstar) ==
    (* Initialize a FIFO queue with a sequence of <pj,p> tuples, 
       where p are pj's successors (except pk) *)
    LET (* <p, ps> tuples, where ps \in Successors(G, p) \ F[pi][p] 
            NOTE: if p = pj, then F[pi][pj] = {pk} (if not, pj whould already have some successors in gi_pstar *)
         Next(p) == IF p = pj THEN ExactSeqFor(Successors(G, pj) \ {pk})
                    ELSE ExactSeqFor({ps \in Successors(G, p) : ps \notin F[pi][p]})
         NewEdges(p) == [i \in 1..Len(Next(p)) |-> <<p, Next(p)[i]>>] 
         (* Update the tracking digraph tg for every tuple in Q *)
         fun[Q \in Seq(Server \X Server), tg \in DigraphType(Server)] ==
            IF Q = << >> THEN tg
            ELSE LET pp == Head(Q)[1]   \* Head(Q) is the next tuple from Q
                     p == Head(Q)[2]
                 IN IF p \notin gi_pstar.node \* p is not yet suspected by pi to have p_star's message
                        THEN IF F[pi][p] # {} \* pi knows already of p's failure 
                                THEN (* Add a sequence of <p,ps> tuples to the FIFO queue *)
                                     fun[Tail(Q) \o NewEdges(p), 
                                         [tg EXCEPT !.node = tg.node \cup {p}, 
                                                    !.edge = tg.edge \cup {<<pp,p>>}]]
                        ELSE fun[Tail(Q), 
                                 [tg EXCEPT !.node = tg.node \cup {p}, 
                                            !.edge = tg.edge \cup {<<pp,p>>}]]
                    ELSE fun[Tail(Q),
                             [tg EXCEPT !.edge = tg.edge \cup {<<pp,p>>}]]   
     IN fun[NewEdges(pj), gi_pstar] 
     
 -----------------------------------------------------------------------------
(* Tracking digraph properties *)
     
(* A non-empty tracking digraph contains always its root *)
TDHasRoot(tg, pj) ==
        pj \in tg.node
                
(* A tracking digraph contains all the successors of every other failed node 
   from the digraph, except those successors that already sent failure notifications.
   Note: F[pi][p] contains the servers that notified pi of p's failure *)
TDFaultyNodeInvariant(tg, pi) ==   
        \A p \in tg.node : F[pi][p] # {} =>   
                \A ps \in Successors(G,p) \ F[pi][p] : ps \in tg.node
        
(* A tracking digraph contains only servers that are either the root or 
   are the successor of another faulty node from the digraph. 
   Note that these two conditions are sufficient to ensure that there 
   is a path from the root to any other server. *)
TDNodeInvariant(tg, pi, pj) ==
    /\ \A p \in tg.node : \/ p = pj
                          \/ \E q \in tg.node : F[pi][q] # {} /\ p \in Successors(G,q) \ F[pi][q]
                
(* A tracking digraph contains only edges that connect a failed node with all its successors, 
   except those successors that already sent failure notifications.
   Note: F[pi][p] contains the servers that notified pi of p's failure *) 
TDEdgeInvariant(tg, pi) == 
        tg.edge = {e \in tg.node \X tg.node : /\ F[pi][e[1]] # {} 
                                              /\ e[2] \in Successors(G, e[1]) \ F[pi][e[1]]}                                           

 -----------------------------------------------------------------------------        

(* Update pi's suspicion of who has p_star's message 
   as a result of receiving pk's notification of pj's failure 
   TLAPS version -- no recursive function 
   Yet, no good for TLC because CHOOSE tg \in DigraphType(Server)
   will result in "Attempted to construct a set with too many elements" *) 
UpdateTrackingDigraphTLAPS(pi, pj, pk, p_star, gi_pstar) ==
    CHOOSE tg \in DigraphType(Server) : /\ TDHasRoot(tg, p_star)
                                        /\ TDFaultyNodeInvariant(tg, pi) 
                                        /\ TDNodeInvariant(tg, pi, p_star) 
                                        /\ TDEdgeInvariant(tg, pi)

(* 
   Operator used by TLAPS to construct a tracking digraphs; due to AreConnectedViaFailures, 
   it's not suitable for TLC. 
   
   Construct the digraph used by pi to track pj's message.
*) 
TrackingDigraph(pi, pj) ==
    LET (* Clearly, a complete digraph satisfies both TDHasRoot and TDFaultyNodeInvariant;
           however, Kn doesn't satisfy TDNodeInvariant. So, let's remove those nodes that  
           don't satisfy TDNodeInvariant, i.e., servers which are neither pj nor 
           are connected through failures to pj *)
        successor(q) == Successors(G, q) \ F[pi][q] \* new definition of successor     
        edges == {e \in Server \X Server : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
        tg_nodes == {p \in Server : AreConnectedViaFailures(pj, p, [node |-> Server, edge |-> edges], F[pi])}
        tg_edges == {e \in tg_nodes \X tg_nodes : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
    IN [node |-> tg_nodes, edge |-> tg_edges] 


THEOREM TDConstruction ==
    ASSUME NEW pi \in Server,
           NEW pj \in Server
    PROVE LET tg == TrackingDigraph(pi, pj)
          IN /\ TDHasRoot(tg, pj)
             /\ TDFaultyNodeInvariant(tg, pi)
             /\ TDNodeInvariant(tg, pi, pj)
             /\ TDEdgeInvariant(tg, pi)
    <1> DEFINE successor(q) == Successors(G, q) \ F[pi][q]
    <1> DEFINE edges == {e \in Server \X Server : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
    <1> DEFINE tmp_tg == [node |-> Server, edge |-> edges]                                      
    <1> DEFINE tg_nodes == {p \in tmp_tg.node : AreConnectedViaFailures(pj, p, tmp_tg, F[pi])}
    <1> DEFINE tg_edges == {e \in tg_nodes \X tg_nodes : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
    <1> DEFINE tg == [node |-> tg_nodes, edge |-> tg_edges]
    <1> HIDE DEF tg, tg_nodes, tg_edges
    <1>1. tmp_tg \in DigraphType(Server) 
        BY ONLY DEF DigraphType                
    <1>2. TDHasRoot(tg, pj) 
        BY ONLY DEF AreConnectedViaFailures, tg, tg_nodes, TDHasRoot 
    <1>3. TDFaultyNodeInvariant(tg, pi)
        <2>1. SUFFICES ASSUME NEW p \in tg.node,
                              F[pi][p] # {},
                              NEW ps \in successor(p)
                     PROVE ps \in tg.node
            BY DEF TDFaultyNodeInvariant
        <2>2. p \in Server BY ONLY DEF tg, tg_nodes
        <2>3. ps \in Server BY ONLY GnodesSrv DEF  Successors
        <2>4. AreConnectedViaFailures(pj, p, tmp_tg, F[pi])
            BY ONLY <2>1 DEF tg, tg_nodes
        <2>5. <<p,ps>> \in edges BY ONLY <2>1, <2>2, <2>3
        <2> SUFFICES AreConnectedViaFailures(pj, ps, tmp_tg, F[pi])
            BY <2>3 DEF tg, tg_nodes
        <2>6. CASE p = pj
            <3> DEFINE P == <<p,ps>>
            <3>1. P \in Seq(tmp_tg.node) BY ONLY <2>2, <2>3
            <3>2. P # <<>> OBVIOUS
            <3>3. \A i \in 1..(Len(P)-1) : <<P[i], P[i+1]>> \in tmp_tg.edge
                BY ONLY <2>5
            <3>4. P \in Path(tmp_tg) BY ONLY <3>1, <3>2, <3>3 DEF Path
            <3>5. P[1] = pj BY ONLY <2>6
            <3>6. P[Len(P)] = ps OBVIOUS
            <3>7. \A i \in 1..Len(P)-1 : F[pi][P[i]] # {}
                BY ONLY <3>5, <2>6, <2>1
            <3> QED BY ONLY <3>4, <3>5, <3>6, <3>7 DEF AreConnectedViaFailures     
        <2>7. CASE p # pj
            <3>1. PICK P \in Path(tmp_tg) : 
                        /\ (P[1] = pj) 
                        /\ (P[Len(P)] = p) 
                        /\ (\A i \in 1..Len(P)-1 : F[pi][P[i]] # {})
                BY ONLY <2>7, <2>4 DEF AreConnectedViaFailures
            <3> DEFINE extP == P \o <<ps>>
            <3>2. extP \in Seq(tmp_tg.node) BY ONLY <3>1, <2>3 DEF Path
            <3>3. extP \in Path(tmp_tg) BY ONLY <3>1, <3>2, <2>5 DEF Path
            <3>4. extP[1] = pj BY ONLY <3>1 DEF Path
            <3>5. extP[Len(extP)] = ps OBVIOUS 
            <3>6. \A i \in 1..Len(extP)-1 : F[pi][extP[i]] # {}
                BY ONLY <3>1, <2>1
            <3> QED BY ONLY <3>3, <3>4, <3>5, <3>6 DEF AreConnectedViaFailures
        <2> QED BY ONLY <2>6, <2>7    
    <1>4. TDNodeInvariant(tg, pi, pj)
        <2>1. SUFFICES ASSUME NEW p \in tg.node \ {pj}
                       PROVE \E q \in tg.node : F[pi][q] # {} /\ p \in successor(q)
            BY DEF TDNodeInvariant
        <2>2. AreConnectedViaFailures(pj, p, tmp_tg, F[pi])
            BY <2>1 DEF tg, tg_nodes
        <2>3. PICK P \in Path(tmp_tg) : 
                    /\ (P[1] = pj) 
                    /\ (P[Len(P)] = p) 
                    /\ (\A i \in 1..Len(P)-1 : F[pi][P[i]] # {})
            BY ONLY <2>1, <2>2 DEF AreConnectedViaFailures
        <2>4. Len(P) > 1 BY ONLY <2>3, <2>1 DEF Path     
        <2>5. F[pi][P[Len(P)-1]] # {} BY ONLY <2>4, <2>3
        <2>6. <<P[Len(P)-1], P[Len(P)]>> \in edges BY ONLY <2>3, <2>4 DEF Path
        <2>7. P[Len(P)] \in successor(P[Len(P)-1]) BY ONLY <2>6
        <2>8. P[Len(P)-1] \in tg.node
            <3>1. P[Len(P)-1] \in Server BY ONLY <2>3 DEF Path 
            <3> SUFFICES AreConnectedViaFailures(pj, P[Len(P)-1], tmp_tg, F[pi])
                BY <2>3, <3>1 DEF tg, tg_nodes
            <3>2. CASE P[Len(P)-1] = pj
                BY ONLY <3>2 DEF AreConnectedViaFailures
            <3>3. CASE P[Len(P)-1] # pj
                <4>1. Len(P) > 2 BY ONLY <2>4, <2>3, <3>3
                <4> DEFINE preP == SubSeq(P, 1, Len(P)-1) 
                <4>2. preP \in Seq(tmp_tg.node) BY ONLY <2>3 DEF Path
                <4>3. \A i \in 1..(Len(preP)-1) : <<preP[i], preP[i+1]>> \in tmp_tg.edge
                    BY ONLY <2>3 DEF Path
                <4>4. preP \in Path(tmp_tg) BY ONLY <4>1, <4>2, <4>3 DEF Path
                <4>5. preP[1] = pj BY ONLY <2>3 DEF Path
                <4>6. preP[Len(preP)] = P[Len(P)-1] BY ONLY <4>1
                <4>7. \A i \in 1..Len(preP)-1 : F[pi][preP[i]] # {}
                    BY ONLY <2>3, <4>1  
                <4> QED BY ONLY <4>4, <4>5, <4>6, <4>7 DEF AreConnectedViaFailures
            <3> QED BY ONLY <3>2, <3>3         
        <2> QED BY ONLY <2>8, <2>7, <2>6, <2>3
    <1>5. TDEdgeInvariant(tg, pi)
        BY DEF TDEdgeInvariant, tg, tg_edges    
    <1> QED BY ONLY <1>1, <1>2, <1>3, <1>4, <1>5 DEF tg, tg_nodes, tg_edges, TrackingDigraph


=============================================================================
