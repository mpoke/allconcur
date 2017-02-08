(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE ReconstructedTD ----------------------

EXTENDS AllConcur, SequenceTheorems, FiniteSetTheorems, TypeInvariant_proofs, TLAPS

THEOREM FunctionExcept2 ==
  ASSUME NEW S, NEW T, NEW fun \in [S -> T], NEW s \in S, NEW e \in T 
  PROVE  [fun EXCEPT ![s] = e][s] = e
    OBVIOUS
THEOREM FunctionExcept3 ==
  ASSUME NEW S1, NEW S2, NEW T, NEW fun \in [S1 -> [S2 -> T]], NEW s1 \in S1, NEW s2 \in S2, NEW e \in T 
  PROVE  [fun EXCEPT ![s1][s2] = e][s1][s2] = e
    OBVIOUS        
    
-----------------------------------------------------------------------------

(* A reconstructed tracking digraph contains always its root *)
RTDHasRoot(tg, pj) == pj \in tg.node

(* A reconstructed tracking digraph contains all the successors of every other 
   failed node from the digraph.
   Note: F[pi][p] contains the servers that notified pi of p's failure *)
RTDFaultyNodeInvariant(tg, pi) == \A p \in tg.node : F[pi][p] # {} =>   
                                            \A ps \in Successors(G,p) : ps \in tg.node
                                            
(* A reconstructed tracking digraph contains only servers that are either the root or 
   are the successor of another faulty node from the digraph. 
   Note that these two conditions are sufficient to ensure that there 
   is a path from the root to any other server. *)
RTDNodeInvariant(tg, pi, pj) ==
    /\ \A p \in tg.node : \/ p = pj
                          \/ \E q \in tg.node : F[pi][q] # {} /\ p \in Successors(G,q) 
 
(* Reconstruct, from failure notifications, the digraph used by pi to track pj's message;
   the reconstructed digraph gr is pesimistic, i.e., servers are never removed, which means
   that the tracking never stops. *)          
ReconstructedTD(pi, pj) ==        
        LET (* Clearly, a complete digraph satisfies RTDHasRoot and RTDFaultyNodeInvariant;
               however, it doesn't satisfy RTDNodeInvariant. So, let's remove those nodes that  
               don't satisfy RTDNodeInvariant, i.e., servers which are neither the root nor 
               are connected via failures to the root *)                                        
            edges == {e \in Server \X Server :  F[pi][e[1]] # {} /\ e \in G.edge}                                        
            rtg_nodes == {p \in Server : AreConnectedViaFailures(pj, p, [node |-> Server, edge |-> edges], F[pi])}
            (* The edges are irrelevant for the above properties; yet, we need them for the RTDInvariant. 
               Initially, consider all edges that connect a failed node to it's successors. *) 
            all_rtg_edges == {e \in rtg_nodes \X rtg_nodes : F[pi][e[1]] # {} /\ e \in G.edge}
                                            \*/\ (e[2] \notin F[pi][e[1]] \/ pj \in M[e[2]])}
            (* Then, remove only those edges on which we can be sure that mj was not transmitted. 
               Note that some of the remaining edges also were not used to transmit mj, but we don't 
               care, since in that case, pi already received mj, hence the tracking is over. *)
            rtg_edges == all_rtg_edges \ {e \in all_rtg_edges : e[2] \in F[pi][e[1]] /\ pj \notin M[pi]}          
        IN [node |-> rtg_nodes, edge |-> rtg_edges]

(* Proof that a reconstructed tracking digraph satisfies the three properties above *)
THEOREM RTDConstruction ==
    ASSUME NEW pi \in Server,
           NEW pj \in Server
    PROVE LET rtg == ReconstructedTD(pi, pj)
          IN /\ RTDHasRoot(rtg, pj)
             /\ RTDFaultyNodeInvariant(rtg, pi)
             /\ RTDNodeInvariant(rtg, pi, pj)
    <1> DEFINE edges == {e \in Server \X Server :  F[pi][e[1]] # {} /\ e \in G.edge}  
    <1> DEFINE tg == [node |-> Server, edge |-> edges]                                      
    <1> DEFINE rtg_nodes == {p \in tg.node : AreConnectedViaFailures(pj, p, tg, F[pi])}
    <1> DEFINE all_rtg_edges == {e \in rtg_nodes \X rtg_nodes : F[pi][e[1]] # {} /\ e \in G.edge}
    <1> DEFINE rtg_edges == all_rtg_edges \ {e \in all_rtg_edges : e[2] \in F[pi][e[1]] /\ pj \notin M[pi]}
    <1> DEFINE rtg == [node |-> rtg_nodes, edge |-> rtg_edges]
    <1> HIDE DEF rtg 
    <1>1. tg \in DigraphType(Server) 
        BY DEF DigraphType, rtg                
    <1>2. RTDHasRoot(rtg, pj) 
        BY DEF AreConnectedViaFailures, rtg, RTDHasRoot
    <1>3. RTDFaultyNodeInvariant(rtg, pi)
        <2> SUFFICES ASSUME NEW p \in rtg.node,
                            F[pi][p] # {}
                     PROVE \A ps \in Successors(G,p) : ps \in rtg.node
            BY DEF RTDFaultyNodeInvariant
        <2>1. \A ps \in Successors(G,p) : ps \in tg.node   
            BY DEF Successors, G, AreConnectedViaFailures, Path, rtg
        <2> SUFFICES ASSUME NEW ps \in tg.node,
                                ps \in Successors(G, p)
                     PROVE ps \in rtg_nodes
            BY <2>1 DEF rtg
        <2>2. AreConnectedViaFailures(pj, p, tg, F[pi]) 
            BY DEF rtg
        <2>3. <<p,ps>> \in tg.edge 
            BY DEF Successors, G, rtg                
        <2> SUFFICES AreConnectedViaFailures(pj, ps, tg, F[pi])
            BY DEF rtg  
        <2>4. CASE p = pj
            <3> DEFINE path == <<p, ps>> 
            <3>1. path \in Path(tg) BY <2>3 DEF Path
            <3>2. \A i \in 1..Len(path)-1 : F[pi][path[i]] # {} OBVIOUS 
            <3> QED BY <2>4, <3>1, <3>2 DEF Path, AreConnectedViaFailures
        <2>5. CASE p # pj   
            <3>1. PICK path \in Path(tg) : /\ path[1] = pj 
                                           /\ path[Len(path)] = p
                                           /\ \A i \in 1..Len(path)-1 : F[pi][path[i]] # {}
                BY <2>2, <2>5 DEF AreConnectedViaFailures
            <3> DEFINE new_path == Append(path, ps)
            <3>2. new_path \in Path(tg) BY <2>3, <3>1 DEF Path  
            <3>3. new_path[1] = pj BY <2>2, <3>1 DEF Path
            <3>4. new_path[Len(new_path)] = ps OBVIOUS
            <3>5. \A i \in 1..Len(new_path)-1 : F[pi][new_path[i]] # {}
                <4>1. \A i \in 1..Len(path)-1 : F[pi][path[i]] # {} BY ONLY <3>1
                <4>2. F[pi][p] # {} OBVIOUS
                <4>3. \A i \in 1..Len(path) : F[pi][path[i]] # {} 
                    BY ONLY <3>1, <4>1, <4>2 DEF rtg
                <4> QED BY <4>3
            <3> QED BY ONLY <2>5, <3>1, <3>2, <3>3, <3>4, <3>5 DEF AreConnectedViaFailures
        <2> QED BY <2>4, <2>5             
    <1>4. RTDNodeInvariant(rtg, pi, pj)
        <2> SUFFICES ASSUME NEW p \in rtg.node \ {pj}
                     PROVE \E q \in rtg.node : F[pi][q] # {} /\ p \in Successors(G,q)
            BY DEF RTDNodeInvariant
        <2>1. PICK path \in Path(tg) : /\ path[1] = pj 
                                       /\ path[Len(path)] = p
                                       /\ \A i \in 1..Len(path)-1 : F[pi][path[i]] # {}  
              BY DEF AreConnectedViaFailures, rtg
        <2> DEFINE q == path[Len(path)-1]
        <2>2. p \in Successors(G,q) BY <2>1 DEF Successors, G, Path   
        <2>3. F[pi][q] # {}
            <3>1. Len(path)-1 \in 1..Len(path)-1 BY <2>1 DEF Path 
            <3> QED BY <2>1, <3>1
        <2>4. q \in tg.node BY <2>1, <2>2, <2>3 DEF Path
        <2>5. AreConnectedViaFailures(pj, q, tg, F[pi])
            <3> DEFINE new_path == SubSeq(path, 1, Len(path)-1)
            <3>1. new_path \in Path(tg) BY <2>1 DEF Path, G
            <3>2. new_path[1] = pj BY <2>1 DEF Path
            <3>3. new_path[Len(new_path)] = q BY <2>1 DEF Path
            <3>4. \A i \in 1..Len(new_path)-1 : F[pi][new_path[i]] # {}
                <4>1. \A i \in 1..Len(new_path) : new_path[i] = path[i] 
                    BY <2>1 DEF Path
                <4>2. \A i \in 1..Len(new_path) : F[pi][new_path[i]] # {} 
                    BY <4>1, <2>1 DEF Path
                <4>3. 1..Len(new_path)-1 \subseteq 1..Len(new_path)
                    <5> HIDE DEF new_path
                    <5>1. Len(new_path) \in Nat BY <2>1 DEF Path, new_path 
                    <5> QED BY ONLY <5>1 
                <4> QED BY <4>1, <4>2, <4>3, <2>1 DEF Path 
            <3> QED BY <3>1, <3>2, <3>3, <3>4 DEF AreConnectedViaFailures
        <2> QED BY <2>2, <2>3, <2>4, <2>5 DEF AreConnectedViaFailures, rtg   
    <1> QED BY ONLY <1>1, <1>2, <1>3, <1>4  DEF rtg, ReconstructedTD
        
-----------------------------------------------------------------------------

(* At any time, a tracking digraph can have one of the following values: 
    - [node |-> {pj}, edge |-> {}] in the initial state 
    - [node |-> {}, edge |-> {}] when done tracking (due to either pruning or receiving the message)
    - TrackingDigraph(pi,pj) during the tracking *)             
PTD == \* Possible Tracking Digraphs
    \A pi, pj \in Server : 
            \/ (g[pi][pj] = [node |-> {pj}, edge |-> {}] /\ F[pi][pj] = {})  \* init
            \/ g[pi][pj] = [node |-> {}, edge |-> {}]      \* end
            \/ g[pi][pj] = TrackingDigraph(pi,pj)         \* during
THEOREM InitPTDInv == Init => PTD 
    BY DEF Init, PTD

THEOREM NextPTDInv == TypeInvariant /\ PTD /\ Next => PTD'
    <1> SUFFICES ASSUME /\ TypeInvariant 
                 PROVE PTD /\ Next => PTD'
        OBVIOUS
    <1>1. SUFFICES /\ (PTD /\ \E p \in Server : Abcast(p)) => PTD'
                   /\ (PTD /\ \E p \in Server : TXMessage(p)) => PTD'
                   /\ (PTD /\ \E p \in Server : ReceiveMessage(p)) => PTD'
                   /\ (PTD /\ \E p \in Server : Adeliver(p)) => PTD'
                   /\ (PTD /\ \E p \in Server : Fail(p)) => PTD'
                   /\ (PTD /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => PTD'
        BY DEF Next 
    <1> DEFINE PTDopts(pi, pj) == 
                    \/ (g[pi][pj] = [node |-> {pj}, edge |-> {}] /\ F[pi][pj] = {})  \* init
                    \/ g[pi][pj] = [node |-> {}, edge |-> {}]      \* end
                    \/ g[pi][pj] = TrackingDigraph(pi,pj)         \* during
    <1> HIDE DEF PTDopts 
    (* Prove that PTD is preserved by Abcast(p) *)
    <1>2. ASSUME PTD, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE PTD'
        <2>1. SUFFICES ASSUME NEW pi \in Server,
                              NEW pj \in Server,
                              PTDopts(pi, pj)
                       PROVE PTDopts(pi, pj)'
            BY <1>2 DEF PTDopts, PTD
        <2>2. UNCHANGED <<F>> BY <1>2 DEF Abcast
        <2>3. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
            BY ONLY <2>2 DEF TrackingDigraph
        <2>4. CASE p = pj
            <3>1. CASE p = pi
                <4>1. g'[pi][pj] = [node |-> {}, edge |-> {}]
                    BY <1>2, <2>4, <3>1 DEF Abcast, TypeInvariant
                <4> QED BY ONLY <4>1, <2>1 DEF PTDopts
            <3>2. CASE p # pi
                <4>1. UNCHANGED <<g[pi][pj]>> 
                    BY <3>2, <1>2 DEF Abcast, TypeInvariant
                <4> QED BY ONLY <4>1, <2>3, <2>2, <2>1 DEF PTDopts
            <3> QED BY ONLY <3>1, <3>2
        <2>5. CASE p # pj
            <3>1. UNCHANGED <<g[pi][pj]>> 
                BY <2>5, <1>2 DEF Abcast, TypeInvariant
            <3> QED BY ONLY <3>1, <2>3, <2>2, <2>1 DEF PTDopts 
        <2> QED BY ONLY <2>4, <2>5
    (* Prove that PTD is preserved by TXMessage(p) *)      
    <1>3. ASSUME PTD, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE PTD'
        BY <1>3 DEF TXMessage, PTD, TrackingDigraph
    (* Prove that PTD is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME PTD, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE PTD'
        <2>1. SUFFICES ASSUME NEW pi \in Server,
                          NEW pj \in Server,
                          PTDopts(pi, pj)
                   PROVE PTDopts(pi, pj)'
            BY <1>4 DEF PTDopts, PTD
        <2> DEFINE m == recvMsg'    
        <2>2. CASE m.type = "BCAST"
            <3>1. UNCHANGED <<F>> BY <1>4, <2>2 DEF ReceiveMessage
            <3>2. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                BY ONLY <3>1 DEF TrackingDigraph
            <3>3. \/ UNCHANGED <<g[pi][pj]>> 
                  \/ g' = [g EXCEPT ![p][p] = [node |-> {}, edge |-> {}], 
                                   ![p][m.owner] = [node |-> {}, edge |-> {}]]
                  \/ g' = [g EXCEPT ![p][m.owner] = [node |-> {}, edge |-> {}]] 
                BY <1>4, <2>2 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant 
            <3>4. CASE UNCHANGED <<g[pi][pj]>> 
                BY ONLY <2>1, <3>1, <3>2, <3>4 DEF PTDopts
            <3>5. CASE g' = [g EXCEPT ![p][p] = [node |-> {}, edge |-> {}], 
                                   ![p][m.owner] = [node |-> {}, edge |-> {}]]
                <4>1. CASE p = pi /\ (p = pj \/ m.owner = pj)
                    <5>1. g'[pi][pj] = [node |-> {}, edge |-> {}]
                        BY <3>5, <4>1 DEF TypeInvariant
                    <5> QED BY ONLY <5>1, <2>1 DEF PTDopts
                <4>2. CASE p # pi \/ (p # pj /\ m.owner # pj)
                    <5>1. UNCHANGED <<g[pi][pj]>> 
                        BY <3>5, <4>2 DEF TypeInvariant
                    <5> QED BY ONLY <2>1, <3>1, <3>2, <5>1 DEF PTDopts 
                <4> QED BY ONLY <4>1, <4>2
            <3>6. CASE g' = [g EXCEPT ![p][m.owner] = [node |-> {}, edge |-> {}]]
                <4>1. CASE p = pi /\ m.owner = pj
                    <5>1. g'[pi][pj] = [node |-> {}, edge |-> {}]
                        BY <3>6, <4>1 DEF TypeInvariant
                    <5> QED BY ONLY <5>1, <2>1 DEF PTDopts
                <4>2. CASE p # pi \/ m.owner # pj
                    <5>1. UNCHANGED <<g[pi][pj]>> 
                        BY <3>6, <4>2 DEF TypeInvariant
                    <5> QED BY ONLY <2>1, <3>1, <3>2, <5>1 DEF PTDopts 
                <4> QED BY ONLY <4>1, <4>2           
            <3> QED BY ONLY <3>3, <3>4, <3>5, <3>6
        <2>3. CASE m.type = "FAIL"
            <3>1. CASE m.owner \in F[p][m.target]
                <4>1. UNCHANGED <<F, g>> 
                    BY ONLY <1>4, <2>3, <3>1 DEF ReceiveMessage, ReceiveFAIL
                <4>2. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                    BY ONLY <4>1 DEF TrackingDigraph
                <4> QED BY <2>1, <4>1, <4>2 DEF PTDopts 
            <3>2. CASE m.owner \notin F[p][m.target]
                <4>1. F' = [F EXCEPT ![p][m.target] = F[p][m.target] \cup {m.owner}]
                    BY ONLY <1>4, <2>3, <3>2 DEF ReceiveMessage, ReceiveFAIL
                <4> DEFINE PruneAllFaulty(p_star, tg) ==
                        IF \A q \in tg.node : F[p][q] # {} THEN [node |-> {}, edge |-> {}] ELSE tg
                <4> HIDE DEF PruneAllFaulty
                <4>2. g' = [g EXCEPT ![p] = [p_star \in Server |->     
                            IF m.target \notin g[p][p_star].node THEN g[p][p_star] 
                            ELSE PruneAllFaulty(p_star, TrackingDigraph(p, p_star))']]
                    BY ONLY <1>4, <2>3, <3>2 DEF ReceiveMessage, ReceiveFAIL, PruneAllFaulty
                <4>3. CASE pi # p
                    <5>1. UNCHANGED <<F[pi], g[pi]>> 
                        BY <4>1, <4>2, <4>3 DEF TypeInvariant
                    <5>2. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                        BY ONLY <5>1 DEF TrackingDigraph
                    <5> QED BY ONLY <2>1, <5>1, <5>2 DEF PTDopts                    
                <4>4. CASE pi = p
                    <5>1. \/ (g'[pi][pj] = g[pi][pj] /\ m.target \notin g[pi][pj].node)
                          \/ g'[pi][pj] = [node |-> {}, edge |-> {}]
                          \/ g'[pi][pj] = TrackingDigraph(pi, pj)'
                        BY <4>4, <4>2 DEF TypeInvariant, PruneAllFaulty
                    <5>2. CASE  \/ g'[pi][pj] = [node |-> {}, edge |-> {}]
                                \/ g'[pi][pj] = TrackingDigraph(pi, pj)'
                        BY ONLY <5>2, <2>1 DEF PTDopts 
                    <5>3. CASE g'[pi][pj] = g[pi][pj] /\ m.target \notin g[pi][pj].node
                        <6>1. CASE g[pi][pj] = [node |-> {pj}, edge |-> {}] /\ F[pi][pj] = {}
                            <7>1. pj # m.target BY ONLY <5>3, <6>1
                            <7>2. UNCHANGED <<F[pi][pj]>> BY <4>1, <4>4, <7>1 DEF TypeInvariant
                            <7> QED BY ONLY <2>1, <5>3, <6>1, <7>2 DEF PTDopts
                        <6>2. CASE g[pi][pj] = [node |-> {}, edge |-> {}] 
                            BY ONLY <6>2, <5>3, <2>1 DEF PTDopts
                        <6>3. CASE g[pi][pj] = TrackingDigraph(pi,pj)
                            <7> SUFFICES TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                                BY <2>1, <5>3, <6>3 DEF PTDopts
                            <7>1. m.target \notin TrackingDigraph(pi,pj).node 
                                BY ONLY <5>3, <6>3
                            <7>2. \A srv \in Server : srv # m.target => UNCHANGED <<F[pi][srv]>>
                                BY <4>1, <4>4 DEF TypeInvariant
                            <7>3. m.owner \in Server /\ m.target \in Server  
                                BY <1>4, <2>3, NextTypeInv DEF TypeInvariant, NetTypeInvariant, Message, NextTypeInv, Next     
                            <7>4. F'[pi][m.target] = F[pi][m.target] \cup {m.owner}
                                BY <4>1, <4>4, <7>3 DEF TypeInvariant
                            <7> DEFINE successor(q) == Successors(G, q) \ F[pi][q] \* new definition of successor
                            <7> DEFINE edges == {e \in Server \X Server : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
                            <7> DEFINE tg_nodes == {srv \in Server : AreConnectedViaFailures(pj, srv, [node |-> Server, edge |-> edges], F[pi])}
                            <7> DEFINE tg_edges == {e \in tg_nodes \X tg_nodes : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
                            <7> SUFFICES tg_nodes = tg_nodes' /\ tg_edges = tg_edges'
                                BY DEF TrackingDigraph 
                            <7> HIDE DEF tg_nodes, tg_edges
                            <7>5. ASSUME NEW q \in tg_nodes 
                                  PROVE q \in tg_nodes'
                                <8>1. SUFFICES ASSUME q \notin tg_nodes'
                                             PROVE FALSE
                                    OBVIOUS
                                <8>2. pj # q BY ONLY <8>1 DEF tg_nodes, AreConnectedViaFailures    
                                <8>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi]) 
                                    BY ONLY <7>5 DEF tg_nodes
                                <8>4. PICK P \in Path([node |-> Server, edge |-> edges]) : 
                                            /\ (P[1] = pj) 
                                            /\ (P[Len(P)] = q) 
                                            /\ (\A i \in 1..Len(P)-1 : F[pi][P[i]] # {})
                                    BY ONLY <8>2, <8>3 DEF AreConnectedViaFailures
                                <8>5. \A i \in 1..Len(P) : P[i] \in Server BY ONLY <8>4 DEF Path   
                                <8>6. \A i \in 1..Len(P)-1 : F'[pi][P[i]] # {}
                                    BY ONLY <7>2, <7>4, <8>4, <8>5
                                <8>7. \A i \in 1..Len(P)-1 : <<P[i],P[i+1]>> \in edges'
                                    <9>1. \A i \in 1..Len(P) : P[i] \in tg_nodes
                                        <10>1. SUFFICES ASSUME NEW k \in 1..Len(P)
                                                        PROVE P[k] \in tg_nodes
                                            OBVIOUS
                                        <10> DEFINE preP == SubSeq(P,1,k)
                                        <10>2. preP \in Path([node |-> Server, edge |-> edges])
                                            BY ONLY <8>4 DEF Path
                                        <10>3. preP[1] = pj BY ONLY <8>4
                                        <10>4. preP[Len(preP)] = P[k] BY ONLY <8>4
                                        <10>5. \A i \in 1..Len(preP)-1 : F[pi][preP[i]] # {}
                                            BY ONLY <8>4      
                                        <10> QED BY ONLY <8>5, <10>2, <10>3, <10>4, <10>5 
                                                 DEF tg_nodes, AreConnectedViaFailures      
                                    <9>2. \A i \in 1..Len(P) : P[i] # m.target
                                        BY ONLY <9>1, <7>1 DEF tg_nodes, TrackingDigraph 
                                    <9>3. \A i \in 1..Len(P)-1 : P[i+1] \in successor(P[i])'
                                        BY ONLY <9>2, <8>5, <8>4, <7>2 DEF Path, Successors, G
                                    <9> QED BY ONLY <9>3, <8>6, <8>5
                                <8>8. P \in Path([node |-> Server, edge |-> edges'])
                                    BY ONLY <8>4, <8>7 DEF Path
                                <8>9. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])'
                                    BY ONLY <8>8, <8>6, <8>4 DEF AreConnectedViaFailures         
                                <8> QED BY ONLY <8>1, <8>9 DEF tg_nodes
                            <7>6. ASSUME NEW q \in tg_nodes' 
                                  PROVE q \in tg_nodes
                                <8>1. SUFFICES ASSUME q \notin tg_nodes
                                             PROVE FALSE
                                    OBVIOUS
                                <8>2. pj # q BY ONLY <8>1 DEF tg_nodes, AreConnectedViaFailures    
                                <8>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])' 
                                    BY ONLY <7>6 DEF tg_nodes
                                <8>4. PICK P \in Path([node |-> Server, edge |-> edges']) : 
                                            /\ (P[1] = pj) 
                                            /\ (P[Len(P)] = q) 
                                            /\ (\A i \in 1..Len(P)-1 : F'[pi][P[i]] # {})
                                    BY ONLY <8>2, <8>3 DEF AreConnectedViaFailures
                                <8>5. \A i \in 1..Len(P) : P[i] \in Server BY ONLY <8>4 DEF Path
                                <8>6. \A i \in 1..Len(P) : P[i] # m.target
                                    <9>1. SUFFICES ASSUME \E k \in 1..Len(P) : P[k] = m.target
                                                   PROVE FALSE
                                        OBVIOUS
                                    <9>2. PICK k \in 1..Len(P) : /\ P[k] = m.target
                                                                 /\ \A l \in 1..k-1 : P[l] # m.target
                                        <10> DEFINE Prop(k) ==  IF k \in 1..Len(P) 
                                                                    THEN P[k] = m.target 
                                                                    ELSE FALSE
                                        <10> HIDE DEF Prop
                                        <10>1. \E k \in 1..Len(P) : Prop(k) BY ONLY <9>1 DEF Prop  
                                        <10>2. \E k \in Nat : Prop(k) BY ONLY <10>1
                                        <10>3. \E k \in Nat : Prop(k) /\ \A l \in 0..k-1 : ~Prop(l) 
                                            BY ONLY <10>2, SmallestNatural
                                        <10> QED BY ONLY <10>3, <10>1 DEF Prop    
                                    <9> DEFINE preP == SubSeq(P,1,k)   
                                    <9>3. preP[1] = pj BY ONLY <8>4
                                    <9>4. preP[Len(preP)] = P[k] BY ONLY <8>4
                                    <9>5. \A i \in 1..Len(preP)-1 : F'[pi][preP[i]] # {}
                                        BY ONLY <8>4
                                    <9>6. \A i \in 1..Len(preP)-1 : F[pi][preP[i]] # {}
                                        BY ONLY <9>5, <8>5, <9>2, <7>2
                                    <9>7. \A i \in 1..Len(preP)-1 : preP[i+1] \in successor(P[i])
                                        BY ONLY <9>2, <8>5, <8>4, <7>2 DEF Path, Successors, G
                                    <9>8. preP \in Path([node |-> Server, edge |-> edges])
                                        BY ONLY <9>6, <9>7, <8>5 DEF Path         
                                    <9>9. AreConnectedViaFailures(pj, P[k], [node |-> Server, edge |-> edges], F[pi])
                                        BY ONLY <9>3, <9>4, <9>8, <9>6 DEF AreConnectedViaFailures      
                                    <9>10. P[k] \in tg_nodes
                                        BY ONLY <8>5, <9>9 DEF tg_nodes
                                    <9>11. TrackingDigraph(pi,pj).node = tg_nodes BY ONLY DEF TrackingDigraph, tg_nodes 
                                    <9> QED BY ONLY <9>11, <9>10, <9>2, <7>1
                                <8>7. \A i \in 1..Len(P)-1 : F[pi][P[i]] # {}
                                    BY ONLY <8>5, <8>6, <8>4, <7>2
                                <8>8. \A i \in 1..Len(P)-1 : P[i+1] \in successor(P[i])
                                    BY ONLY <8>7, <8>6, <8>5, <8>4, <7>2 DEF Path, Successors, G  
                                <8>9. P \in Path([node |-> Server, edge |-> edges])
                                    BY ONLY <8>4, <8>8, <8>7 DEF Path
                                <8>10. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])
                                    BY ONLY <8>9, <8>7, <8>4 DEF AreConnectedViaFailures           
                                <8> QED BY ONLY <8>1, <8>10, <8>5 DEF tg_nodes
                            <7>7. tg_nodes = tg_nodes' BY ONLY <7>5, <7>6
                            <7>8. m.target \notin tg_nodes BY <7>1 DEF tg_nodes, TrackingDigraph 
                            <7>9. ASSUME NEW e \in tg_edges 
                                  PROVE e \in tg_edges'
                                <8>1. F[pi][e[1]] # {} /\ e[2] \in successor(e[1])
                                    BY ONLY DEF tg_edges
                                <8>2. e[1] \in Server /\ e[2] \in Server
                                    BY ONLY DEF tg_edges, tg_nodes
                                <8>3. F'[pi][e[1]] # {} BY ONLY <8>1, <8>2, <7>2, <7>4
                                <8>4. e[1] # m.target BY ONLY <7>8 DEF tg_edges
                                <8>5. e[2] \in successor(e[1])'
                                    BY ONLY <8>1, <8>2, <8>4, <8>3, <7>2 DEF Successors, G            
                                <8> QED BY ONLY <7>9, <8>3, <8>5, <7>7 DEF tg_edges       
                            <7>10. ASSUME NEW e \in tg_edges' 
                                  PROVE e \in tg_edges
                                <8>1. F'[pi][e[1]] # {} /\ e[2] \in successor(e[1])'
                                    BY ONLY DEF tg_edges
                                <8>2. e[1] \in Server /\ e[2] \in Server
                                    BY ONLY DEF tg_edges, tg_nodes
                                <8>3. e[1] # m.target BY ONLY <7>8, <7>7 DEF tg_edges    
                                <8>4. F[pi][e[1]] # {} BY ONLY <8>1, <8>2, <8>3, <7>2
                                <8>5. e[2] \in successor(e[1])
                                    BY ONLY <8>1, <8>2, <8>4, <8>3, <7>2 DEF Successors, G
                                <8> QED BY ONLY <7>10, <8>4, <8>5, <7>7 DEF tg_edges
                            <7>11. tg_edges = tg_edges' BY ONLY <7>9, <7>10       
                            <7> QED BY ONLY <7>7, <7>11
                        <6> QED BY ONLY <2>1, <6>1, <6>2, <6>2, <6>3 DEF PTDopts
                    <5> QED BY ONLY <5>1, <5>2, <5>3     
                <4> QED BY ONLY <4>3, <4>4
            <3> QED BY ONLY <3>1, <3>2
        <2>4. CASE m.type # "BCAST" /\ m.type # "FAIL"
            <3>1. UNCHANGED <<F, g>> BY <1>4, <2>4 DEF ReceiveMessage
            <3>2. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                BY ONLY <3>1 DEF TrackingDigraph
            <3> QED BY <2>1, <3>1, <3>2 DEF PTDopts
        <2> QED BY ONLY <2>2, <2>3, <2>4
    (* Prove that PTD is preserved by Adeliver(p) *)
    <1>5. ASSUME PTD, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE PTD'
        BY <1>5 DEF Adeliver, PTD, TrackingDigraph
    (* Prove that FDAccuracy is preserved by Fail(p) *)
    <1>6. ASSUME PTD, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE PTD'
        BY <1>6 DEF Fail, PTD, TrackingDigraph
    (* Prove that PTD is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME PTD, 
                 NEW pf \in Server, 
                 NEW pd \in Server,
                 DetectFailure(pf,pd) 
          PROVE PTD'
        BY <1>7 DEF DetectFailure, PTD, TrackingDigraph
    <1> QED BY ONLY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 

THEOREM PTDInv == Spec => []PTD    
    (* Prove stuttering step *) 
    <1>1. PTD /\ UNCHANGED vars => PTD' 
        BY DEF PTD, TrackingDigraph, vars
    (* Prove TypeInvariant *) 
    <1>2. Spec => TypeInvariant BY PTL, TypeInv
    (* Use InitPTDInv and NextPTDInv *)
    <1>3. Spec /\ TypeInvariant => []PTD
        <2> SUFFICES ASSUME Spec, TypeInvariant 
                     PROVE []PTD
            OBVIOUS
        <2> QED BY PTL, InitPTDInv, NextPTDInv, <1>1 DEF Spec    
    <1> QED BY <1>2, <1>3
   
-----------------------------------------------------------------------------    

(* A tracking digraph g is empty (a.k.a. the tracking has stopped) only if either the message was received 
   or all servers in the tracking digraph TD have failed (i.e., PruneAllFaulty).
   Note that once TD has all servers faulty, all future TD (regardless of the received failure notif.) 
   have all servers faulty; thus, once a TD can be prunned, it can no longer be expanded. *)
ETD == \* Empty Tracking Digraph
    \A pi, pj \in Server : g[pi][pj] = [node |-> {}, edge |-> {}] =>
                \/ pj \in M[pi]
                \/ \A q \in TrackingDigraph(pi, pj).node : F[pi][q] # {}
THEOREM InitETDInv == Init => ETD 
    BY DEF Init, ETD

THEOREM NextETDInv == TypeInvariant /\ ETD /\ Next => ETD'
    <1> SUFFICES ASSUME /\ TypeInvariant 
                 PROVE ETD /\ Next => ETD'
        OBVIOUS
    <1>1. SUFFICES /\ (ETD /\ \E p \in Server : Abcast(p)) => ETD'
                   /\ (ETD /\ \E p \in Server : TXMessage(p)) => ETD'
                   /\ (ETD /\ \E p \in Server : ReceiveMessage(p)) => ETD'
                   /\ (ETD /\ \E p \in Server : Adeliver(p)) => ETD'
                   /\ (ETD /\ \E p \in Server : Fail(p)) => ETD'
                   /\ (ETD /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => ETD'
        BY DEF Next
    <1> DEFINE ETD_property(pi, pj) == 
                g[pi][pj] = [node |-> {}, edge |-> {}] =>
                    \/ pj \in M[pi]
                    \/ \A q \in TrackingDigraph(pi, pj).node : F[pi][q] # {}
    <1> HIDE DEF ETD_property                  
    (* Prove that ETD is preserved by Abcast(p) *)
    <1>2. ASSUME ETD, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE ETD'
        <2>1. SUFFICES ASSUME NEW pi \in Server,
                              NEW pj \in Server,
                              ETD_property(pi,pj)
                       PROVE ETD_property(pi,pj)'
            BY <1>2 DEF ETD, ETD_property
        <2>2. UNCHANGED <<F>>
             BY ONLY <1>2 DEF Abcast
        <2>3. TrackingDigraph(pi, pj) = TrackingDigraph(pi, pj)' 
            BY ONLY <2>2 DEF TrackingDigraph         
        <2>4. CASE p # pi
            <3>1. UNCHANGED <<g[pi][pj], M[pi]>> 
                BY <1>2, <2>4 DEF Abcast, TypeInvariant     
            <3> QED BY ONLY <2>1, <2>2, <2>3, <3>1 DEF ETD_property
        <2>5. CASE p = pi
            <3>1. CASE p # pj
                <4>1. UNCHANGED <<g[pi][pj]>> 
                    BY <1>2, <3>1 DEF Abcast, TypeInvariant    
                <4>2. pj \in M[pi] => pj \in M'[pi]
                    BY <2>5, <1>2 DEF Abcast, TypeInvariant     
                <4> QED BY ONLY <2>1, <4>1, <4>2, <2>2, <2>3 DEF ETD_property
            <3>2. CASE p = pj
                <4>1. pj \in M'[pi]
                    BY <2>5, <3>2, <1>2 DEF Abcast, TypeInvariant   
                <4> QED BY ONLY <4>1 DEF ETD_property    
            <3> QED BY ONLY <3>1, <3>2    
        <2> QED BY ONLY <2>4, <2>5
    (* Prove that ETD is preserved by TXMessage(p) *)      
    <1>3. ASSUME ETD, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE ETD'
        BY <1>3 DEF TXMessage, ETD, TrackingDigraph
    (* Prove that ETD is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME ETD, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE ETD'
        <2>1. SUFFICES ASSUME NEW pi \in Server,
                              NEW pj \in Server,
                              ETD_property(pi,pj)
                       PROVE ETD_property(pi,pj)'
            BY <1>4 DEF ETD, ETD_property
        <2> DEFINE m == recvMsg'    
        <2>2. CASE m.type = "BCAST"
            <3>1. UNCHANGED <<F>>
                BY ONLY <1>4, <2>2 DEF ReceiveMessage
            <3>2. TrackingDigraph(pi, pj) = TrackingDigraph(pi, pj)' 
                BY ONLY <3>1 DEF TrackingDigraph
            <3>3. CASE flag.abcast[m.owner] = 1 /\ m.owner \notin M[p]
                <4>1. CASE flag.abcast[p] = 0
                    <5>1. /\ M' = [M EXCEPT ![p] = M[p] \cup {p, m.owner}]
                          /\ g' = [g EXCEPT ![p][p] = [node |-> {}, edge |-> {}], 
                                   ![p][m.owner] = [node |-> {}, edge |-> {}]]
                        BY ONLY <1>4, <2>2, <3>3, <4>1 DEF ReceiveMessage, ReceiveBCAST
                    <5>2. CASE pi = p /\ (pj = p \/ pj = m.owner)
                        <6>1.  pj \in M'[pi]
                            BY <5>2, <5>1 DEF TypeInvariant
                        <6> QED BY ONLY <6>1 DEF ETD_property     
                    <5>3. CASE pi # p \/ (pj # p /\ pj # m.owner)
                        <6>1. UNCHANGED <<g[pi][pj]>> 
                            BY <5>3, <5>1 DEF TypeInvariant
                        <6>2. pj \in M[pi] => pj \in M'[pi]
                            BY <5>3, <5>1 DEF TypeInvariant
                        <6> QED BY ONLY <6>1, <6>2, <3>1, <3>2, <2>1 DEF ETD_property
                    <5> QED BY ONLY <5>2, <5>3 
                <4>2. CASE flag.abcast[p] # 0
                    <5>1. /\ M' = [M EXCEPT ![p] = M[p] \cup {m.owner}]
                          /\ g' = [g EXCEPT ![p][m.owner] = [node |-> {}, edge |-> {}]]
                        BY ONLY <1>4, <2>2, <3>3, <4>2 DEF ReceiveMessage, ReceiveBCAST
                    <5>2. CASE pi = p /\ pj = m.owner
                        <6>1.  pj \in M'[pi]
                            BY <5>2, <5>1 DEF TypeInvariant
                        <6> QED BY ONLY <6>1 DEF ETD_property     
                    <5>3. CASE pi # p \/ pj # m.owner
                        <6>1. UNCHANGED <<g[pi][pj]>> 
                            BY <5>3, <5>1 DEF TypeInvariant
                        <6>2. pj \in M[pi] => pj \in M'[pi]
                            BY <5>3, <5>1 DEF TypeInvariant
                        <6> QED BY ONLY <6>1, <6>2, <3>1, <3>2, <2>1 DEF ETD_property
                    <5> QED BY ONLY <5>2, <5>3
                <4> QED BY ONLY <4>1, <4>2
            <3>4. CASE flag.abcast[m.owner] # 1 \/ m.owner \in M[p]
                <4>1. UNCHANGED <<M, g>>
                    BY ONLY <3>4, <2>2, <1>4 DEF ReceiveMessage, ReceiveBCAST
                <4> QED BY ONLY <2>1, <3>1, <3>2, <4>1 DEF ETD_property       
            <3> QED BY ONLY <3>3, <3>4           
        <2>3. CASE m.type = "FAIL"
            <3>1. UNCHANGED <<M>>
                BY ONLY <1>4, <2>3 DEF ReceiveMessage
            <3>2. CASE m.owner \notin F[p][m.target]
                <4> DEFINE PruneAllFaulty(p_star, tg) ==
                        IF \A q \in tg.node : F[p][q] # {} THEN [node |-> {}, edge |-> {}] ELSE tg
                <4> HIDE DEF PruneAllFaulty        
                <4>1. /\ F' = [F EXCEPT ![p][m.target] = F[p][m.target] \cup {m.owner}]
                      /\ g' = [g EXCEPT ![p] = [p_star \in Server |->
                            IF m.target \notin g[p][p_star].node THEN g[p][p_star] 
                            ELSE PruneAllFaulty(p_star, TrackingDigraph(p, p_star))']]
                    BY ONLY <1>4, <2>3, <3>2 DEF ReceiveMessage, ReceiveFAIL, PruneAllFaulty
                <4>2. CASE p # pi
                    <5>1. UNCHANGED <<g[pi][pj],F[pi]>>
                        BY <4>1, <4>2 DEF TypeInvariant
                    <5>2. TrackingDigraph(pi,pj) = TrackingDigraph(pi,pj)'
                        BY ONLY <5>1 DEF TrackingDigraph   
                    <5> QED BY ONLY <2>1, <3>1, <5>1, <5>2 DEF ETD_property
                <4>3. CASE p = pi
                    <5>1. \/ (/\ g'[pi][pj] = g[pi][pj] 
                              /\ m.target \notin g[pi][pj].node)
                          \/ (/\ g'[pi][pj] = [node |-> {}, edge |-> {}] 
                              /\ \A q \in TrackingDigraph(pi, pj)'.node : F'[pi][q] # {})
                          \/ g'[pi][pj] = TrackingDigraph(pi, pj)'
                        BY <4>3, <4>1 DEF TypeInvariant, PruneAllFaulty
                    <5>2. CASE /\ g'[pi][pj] = g[pi][pj] 
                               /\ m.target \notin g[pi][pj].node
                        <6>1. SUFFICES ASSUME \A q \in TrackingDigraph(pi, pj).node : F[pi][q] # {},
                                              g[pi][pj] = [node |-> {}, edge |-> {}]
                                       PROVE \A q \in TrackingDigraph(pi, pj)'.node : F'[pi][q] # {}
                            BY <2>1, <3>1, <5>2 DEF ETD_property
                        <6>2. \A q \in Server: F[pi][q] # {} => F'[pi][q] # {}
                            BY <4>1, <4>3 DEF TypeInvariant  
                        <6>3. /\ TrackingDigraph(pi, pj).node \subseteq Server  
                              /\ TrackingDigraph(pi, pj)'.node \subseteq Server
                           BY ONLY DEF TrackingDigraph
                        <6>4. SUFFICES TrackingDigraph(pi, pj)'.node \subseteq TrackingDigraph(pi, pj).node
                            BY <6>1, <6>2, <6>3
                        <6> DEFINE successor(q) == Successors(G, q) \ F[pi][q]
                        <6> DEFINE edges == {e \in Server \X Server : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
                        <6> DEFINE tg_nodes == {srv \in Server : AreConnectedViaFailures(pj, srv, [node |-> Server, edge |-> edges], F[pi])}
                        <6>5. /\ TrackingDigraph(pi, pj).node = tg_nodes
                              /\ TrackingDigraph(pi, pj)'.node = tg_nodes'
                            BY ONLY DEF TrackingDigraph
                        <6> HIDE DEF tg_nodes                            
                        <6>6. ASSUME NEW q \in tg_nodes' 
                              PROVE q \in tg_nodes
                             <7>1. SUFFICES ASSUME q \notin tg_nodes
                                           PROVE FALSE
                                OBVIOUS
                            <7>2. pj # q BY ONLY <7>1 DEF tg_nodes, AreConnectedViaFailures    
                            <7>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])' 
                                BY ONLY <6>6 DEF tg_nodes
                            <7>4. PICK P \in Path([node |-> Server, edge |-> edges']) : 
                                        /\ (P[1] = pj) 
                                        /\ (P[Len(P)] = q) 
                                        /\ (\A i \in 1..Len(P)-1 : F'[pi][P[i]] # {})
                                BY ONLY <7>2, <7>3 DEF AreConnectedViaFailures
                            <7>5. \A i \in 1..Len(P) : P[i] \in Server BY ONLY <7>4 DEF Path
                            <7>6. \A srv \in Server : srv # m.target => UNCHANGED <<F[pi][srv]>>
                                BY <4>1, <4>3 DEF TypeInvariant
                            <7>7. m.owner \in Server /\ m.target \in Server  
                                BY <1>4, <2>3, NextTypeInv DEF TypeInvariant, NetTypeInvariant, Message, NextTypeInv, Next     
                            <7>8. F'[pi][m.target] = F[pi][m.target] \cup {m.owner}           
                                BY <4>1, <4>3, <7>7 DEF TypeInvariant
                            <7>9. CASE \/ \A i \in 1..Len(P) : P[i] # m.target
                                       \/ F[pi][m.target] # {}
                                <8>1. \A i \in 1..Len(P)-1 : <<P[i],P[i+1]>> \in edges
                                    <9>1. SUFFICES ASSUME NEW k \in 1..Len(P)-1
                                                   PROVE <<P[k],P[k+1]>> \in edges
                                        OBVIOUS
                                    <9>2. F[pi][P[k]] # {}
                                        BY ONLY <7>9, <7>6, <7>4, <7>5
                                    <9>3. \A srv \in Server : F[pi][srv] \subseteq F'[pi][srv]
                                        BY ONLY <7>6, <7>8 
                                    <9>4. \A srv \in Server : Successors(G, srv)  = Successors(G, srv)'
                                        BY ONLY DEF Successors, G       
                                    <9>5. P[k+1] \in Successors(G, P[k]) \ F[pi][P[k]]
                                        BY ONLY <7>5, <9>3, <9>4, <7>4 DEF Path
                                    <9> QED BY ONLY <7>5, <9>2, <9>5
                                <8>2. P \in Path([node |-> Server, edge |-> edges])
                                    BY ONLY <7>4, <8>1 DEF Path    
                                <8>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])
                                    BY ONLY <8>2, <8>1, <7>4 DEF AreConnectedViaFailures
                                <8> QED BY ONLY <8>3, <7>5, <7>1 DEF tg_nodes 
                            <7>10. CASE /\ \E i \in 1..Len(P) : P[i] = m.target
                                        /\ F[pi][m.target] = {}
                                <8>1. PICK k \in 1..Len(P) : /\ P[k] = m.target
                                                             /\ \A l \in 1..k-1 : P[l] # m.target
                                    <9> DEFINE Prop(k) ==  IF k \in 1..Len(P) 
                                                                THEN P[k] = m.target 
                                                                ELSE FALSE
                                    <9> HIDE DEF Prop
                                    <9>1. \E k \in 1..Len(P) : Prop(k) BY ONLY <7>10 DEF Prop  
                                    <9>2. \E k \in Nat : Prop(k) BY ONLY <9>1
                                    <9>3. \E k \in Nat : Prop(k) /\ \A l \in 0..k-1 : ~Prop(l) 
                                        BY ONLY <9>2, SmallestNatural
                                    <9> QED BY ONLY <9>3, <9>1 DEF Prop        
                                <8>2. m.target # pj
                                    <9>1. pj \in tg_nodes
                                        BY ONLY <6>5, TDConstruction DEF TDHasRoot, G
                                    <9> QED BY ONLY <9>1, <6>5, <7>10, <6>1   
                                <8>3. k > 1 BY ONLY <8>1, <8>2, <7>4
                                <8> DEFINE preP == SubSeq(P,1,k)   
                                <8>4. P[k] \in tg_nodes
                                    <9> SUFFICES AreConnectedViaFailures(pj, P[k], [node |-> Server, edge |-> edges], F[pi])
                                        BY <7>5 DEF tg_nodes
                                    <9>1. \A i \in 1..Len(preP)-1 : UNCHANGED <<F[pi][preP[i]]>>
                                        BY  ONLY <8>1, <7>6, <7>5
                                    <9>2. \A srv \in Server : Successors(G, srv)  = Successors(G, srv)'
                                        BY ONLY DEF Successors, G     
                                    <9>4. \A i \in 1..Len(preP)-1 : <<preP[i],preP[i+1]>> \in edges
                                        BY ONLY <9>1, <9>2, <7>5, <7>4 DEF Path
                                    <9>5. preP \in Path([node |-> Server, edge |-> edges])
                                        BY ONLY <9>4 DEF Path       
                                    <9>6. preP[1] = pj BY <7>4
                                    <9>7. preP[Len(preP)] = P[k] OBVIOUS    
                                    <9>8. \A i \in 1..Len(preP)-1 :  F[pi][preP[i]] # {}
                                        BY ONLY <9>1, <7>4   
                                    <9> QED BY ONLY <9>5, <9>6, <9>7, <9>8 DEF AreConnectedViaFailures
                                <8> QED BY ONLY <8>1, <7>10, <6>5, <6>1, <8>4
                            <7> QED BY ONLY <7>9, <7>10
                        <6> QED BY ONLY <6>4, <6>5, <6>6
                    <5>3. CASE /\ g'[pi][pj] = [node |-> {}, edge |-> {}] 
                               /\ \A q \in TrackingDigraph(pi, pj)'.node : F'[pi][q] # {}
                        BY ONLY <5>3 DEF ETD_property
                    <5>4. CASE g'[pi][pj] = TrackingDigraph(pi, pj)'         
                        <6>1. TrackingDigraph(pi, pj)'.node # {}
                            BY ONLY DEF TrackingDigraph, AreConnectedViaFailures
                        <6>2. TrackingDigraph(pi, pj)' #  [node |-> {}, edge |-> {}]
                            BY ONLY <6>1
                        <6> QED BY ONLY <6>1, <6>2, <5>4, <2>1 DEF ETD_property    
                    <5> QED BY ONLY <5>1, <5>2, <5>3, <5>4
                <4> QED BY ONLY <4>2, <4>3    
            <3>3. CASE m.owner \in F[p][m.target]
                <4>1. UNCHANGED <<F,g>> 
                    BY ONLY <1>4, <2>3, <3>3 DEF ReceiveMessage, ReceiveFAIL
                <4> QED BY ONLY <3>1, <2>1, <4>1 DEF ETD_property, TrackingDigraph   
            <3> QED BY ONLY <3>2, <3>3
        <2>4. CASE m.type # "BCAST" /\ m.type # "FAIL"
            BY <1>4, <2>1, <2>4 DEF ReceiveMessage, ETD_property, TrackingDigraph 
        <2> QED BY ONLY <2>2, <2>3, <2>4
    (* Prove that ETD is preserved by Adeliver(p) *)
    <1>5. ASSUME ETD, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE ETD'
        BY <1>5 DEF Adeliver, ETD, TrackingDigraph
    (* Prove that ETD is preserved by Fail(p) *)
    <1>6. ASSUME ETD, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE ETD'
        BY <1>6 DEF Fail, ETD, TrackingDigraph      
    (* Prove that ETD is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME ETD, 
                 NEW pf \in Server, 
                 NEW pd \in Server,
                 DetectFailure(pf,pd) 
          PROVE ETD'
        BY <1>7 DEF DetectFailure, ETD, TrackingDigraph
    <1> QED BY ONLY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7


THEOREM ETDInv == Spec => []ETD    
    (* Prove stuttering step *) 
    <1>1. ETD /\ UNCHANGED vars => ETD' 
        BY DEF ETD, TrackingDigraph, vars
    (* Prove TypeInvariant *) 
    <1> Spec => TypeInvariant BY PTL, TypeInv
    (* Use InitETDInv and NextETDInv *)
    <1>2. Spec /\ TypeInvariant => []ETD
        <2> SUFFICES ASSUME Spec, TypeInvariant 
                     PROVE []ETD
            OBVIOUS
        <2> QED BY PTL, InitETDInv, NextETDInv, <1>1 DEF Spec    
    <1> QED BY <1>2   

-----------------------------------------------------------------------------
(* RTDInvariant:  If a server p is part of the reconstructed tracking digraph 
   (see below) of pi to track pj's message but not part of the current tracking 
   digraph then pi received pj's message OR pi received a notification of p's 
   failure OR p didn't received pj's message *)
  
RTDInvariant == 
    \A pi, pj \in Server : \A p \in Server : ((p \in ReconstructedTD(pi,pj).node /\ p \notin g[pi][pj].node)
                                => \/ pj \in M[pi]  \* pi stop tracking pj's message
                                   \/ F[pi][p] # {} \* p failed  stop tracking pj's message  
                                   \/ PathsFromTo(ReconstructedTD(pi,pj), pj, p) = {}) \* p is disconnected in RTD

THEOREM InitRTDInv == Init => RTDInvariant
    <1> SUFFICES ASSUME Init 
                 PROVE RTDInvariant
        OBVIOUS
    <1> SUFFICES ASSUME NEW pi \in Server,
                        NEW pj \in Server
                 PROVE ReconstructedTD(pi,pj).node = g[pi][pj].node
        BY DEF RTDInvariant 
    <1> DEFINE edges == {e \in Server \X Server :  F[pi][e[1]] # {} /\ e \in G.edge}
    <1>1. edges = {} BY DEF Init
    <1> HIDE DEF edges
    <1> DEFINE rtg_nodes == {q \in Server : AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges], F[pi])}
    <1>2. rtg_nodes = {pj} BY <1>1 DEF Init, AreConnectedViaFailures, Path
    <1> HIDE DEF rtg_nodes
    <1>3. ReconstructedTD(pi,pj).node = rtg_nodes BY DEF ReconstructedTD, rtg_nodes, edges
    <1> QED BY <1>2, <1>3 DEF Init
    
THEOREM NextRTDInv == (/\ TypeInvariant 
                      /\ PTD \* Possible Tracking Digraphs
                      /\ ETD \* Empty Tracking Digraph
                      /\ RTDInvariant
                      /\ Next) 
                      => RTDInvariant'
    <1> SUFFICES ASSUME /\ TypeInvariant
                        /\ PTD 
                        /\ ETD
                 PROVE RTDInvariant /\ Next => RTDInvariant'
        OBVIOUS                          
    <1>1. SUFFICES /\ (RTDInvariant /\ \E p \in Server : Abcast(p)) => RTDInvariant'
                   /\ (RTDInvariant /\ \E p \in Server : TXMessage(p)) => RTDInvariant'
                   /\ (RTDInvariant /\ \E p \in Server : ReceiveMessage(p)) => RTDInvariant'
                   /\ (RTDInvariant /\ \E p \in Server : Adeliver(p)) => RTDInvariant'
                   /\ (RTDInvariant /\ \E p \in Server : Fail(p)) => RTDInvariant'
                   /\ (RTDInvariant /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => RTDInvariant'
        BY DEF Next
    <1> DEFINE rtd_inv(pi,pj,q) == (q \in ReconstructedTD(pi,pj).node /\ q \notin g[pi][pj].node)
                                        => \/ pj \in M[pi]
                                           \/ F[pi][q] # {}
                                           \/ PathsFromTo(ReconstructedTD(pi,pj), pj, q) = {}  
    <1> HIDE DEF rtd_inv                                          
    (* Prove that RTDInvariant is preserved by Abcast(p) *)
    <1>2. ASSUME RTDInvariant, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE RTDInvariant' 
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>2 DEF RTDInvariant, rtd_inv
        (* Servers can only be added to M *)
        <2>1. pj \in M[pi] => pj \in M'[pi] BY <1>2 DEF Abcast, TypeInvariant
        (* F is unchanged *)
        <2>2. UNCHANGED <<F>> BY <1>2 DEF Abcast, TypeInvariant
        <2> DEFINE RTD == ReconstructedTD(pi,pj)
        <2>3. /\ RTD \in DigraphType(Server) 
              /\ RTD' \in DigraphType(Server) 
            BY DEF DigraphType, ReconstructedTD    
        <2> HIDE DEF RTD
        (* RTD(pi,pj).node is unchanged *)
        <2>4. RTD.node = RTD'.node
            BY <1>2 DEF Abcast, TypeInvariant, RTD, ReconstructedTD, PathsFromTo, Path
        <2> DEFINE all_rtd_edges == {e \in RTD.node \X RTD.node : F[pi][e[1]] # {} /\ e \in G.edge}
        <2> DEFINE rtd_edges == all_rtd_edges \ {e \in all_rtd_edges : e[2] \in F[pi][e[1]] /\ pj \notin M[pi]}
        <2> HIDE DEF rtd_edges
        <2>5. /\ RTD.edge = rtd_edges
              /\ RTD'.edge = rtd_edges' 
            BY DEF RTD, ReconstructedTD, TypeInvariant, rtd_edges
        (* RTD(pi,pj).edges before removing unsued edges is unchanged *)    
        <2>6. all_rtd_edges = all_rtd_edges' BY ONLY <2>2, <2>4   
        <2>7. CASE pi # p \/ (pi = p /\ pj # pi)
            (* g[pi][pj] is unchanged *)
            <3>1. UNCHANGED <<g[pi][pj]>> BY <1>2, <2>7 DEF Abcast, TypeInvariant
            <3> SUFFICES ASSUME PathsFromTo(RTD, pj, q) = {},
                                pj \notin M'[pi] 
                         PROVE PathsFromTo(RTD, pj, q)' = {}
                BY <2>1, <2>2, <2>4, <3>1 DEF RTD, rtd_inv
            <3> SUFFICES ASSUME PathsFromTo(RTD, pj, q)' # {}
                         PROVE FALSE
                OBVIOUS
            (* Assume that there is an edge in RTD' that is not in RTD *)
            <3> SUFFICES ASSUME \E e \in rtd_edges' : e \notin rtd_edges
                         PROVE FALSE
                BY <2>4, <2>5 DEF PathsFromTo, Path        
            <3>2. PICK e \in rtd_edges' : e \notin rtd_edges
                OBVIOUS
            (* This edge must be removed from RTD because it was never used *)       
            <3>3. /\ e[2] \in F[pi][e[1]] /\ pj \notin M[pi]
                  /\ (e[2] \notin F'[pi][e[1]] \/ pj \in M'[pi]) 
                BY ONLY <3>2, <2>6 DEF rtd_edges
            (* pj is added to M[pi] => rtd_inv(pi,pj,q)' *)
            <3>4. pj \notin M[pi] /\ pj \in M'[pi] BY ONLY <2>2, <3>3
            <3> QED BY <3>4
        <2>8. CASE pi = p /\ pj = pi
            (* p is added to M[p] => rtd_inv(p,p,q)' *)
            <3>1. pj \in M'[pi] BY <1>2, <2>8 DEF Abcast, TypeInvariant
            <3> QED BY <3>1 DEF rtd_inv
        <2> QED BY ONLY <2>7, <2>8  
    (* Prove that RTDInvariant is preserved by TXMessage(p) *)      
    <1>3. ASSUME RTDInvariant, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE RTDInvariant'
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>3 DEF RTDInvariant, rtd_inv  
        <2>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' BY <1>3 DEF TXMessage, ReconstructedTD
        <2> QED BY <1>3, <2>1 DEF TXMessage, rtd_inv
    (* Prove that RTDInvariant is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME RTDInvariant, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE RTDInvariant'
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>4 DEF RTDInvariant, rtd_inv
        <2> DEFINE m == recvMsg'        
        <2>1. CASE m.type = "BCAST"
            (* F is unchanged *)
            <3>1. UNCHANGED <<F>> BY <1>4, <2>1 DEF ReceiveMessage    
            <3> DEFINE RTD == ReconstructedTD(pi,pj)
            <3>2. /\ RTD \in DigraphType(Server) 
                  /\ RTD' \in DigraphType(Server) 
                BY DEF DigraphType, ReconstructedTD    
            <3> HIDE DEF RTD
            (* RTD.node is unchanged *)
            <3>3. RTD.node = RTD'.node
                BY <1>4, <2>1, <3>1 DEF RTD, ReconstructedTD, PathsFromTo, Path
            <3> DEFINE all_rtd_edges == {e \in RTD.node \X RTD.node : F[pi][e[1]] # {} /\ e \in G.edge}
            <3> DEFINE rtd_edges == all_rtd_edges \ {e \in all_rtd_edges : e[2] \in F[pi][e[1]] /\ pj \notin M[pi]}
            <3> HIDE DEF rtd_edges
            <3> /\ RTD.edge = rtd_edges
                /\ RTD'.edge = rtd_edges' 
                BY DEF RTD, ReconstructedTD, TypeInvariant, rtd_edges
            (* RTD(pi,pj).edges before removing unsued edges is unchanged *)  
            <3> all_rtd_edges = all_rtd_edges' BY ONLY <3>1, <3>3
            <3>4. CASE flag.abcast[m.owner] = 1 /\ m.owner \notin M[p]
                <4>1. CASE \/ pi # p 
                           \/ (pi = p /\ pj # m.owner /\ pj # p)
                           \/ (pi = p /\ pj # m.owner /\ pj = p /\ flag.abcast[p] # 0)
                    (* g[pi][pj] is unchanged *)
                    <5>1. UNCHANGED <<g[pi][pj]>>
                        <6>1. CASE pi # p 
                            BY <1>4, <2>1, <3>4, <6>1 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
                        <6>2. CASE pi = p /\ pj # m.owner /\ pj # p
                            <7> DEFINE g_p_m_owner(g_p) == [g_p EXCEPT ![m.owner] = [node |-> {}, edge |-> {}]]
                            <7> DEFINE g_p_p(g_p) == [g_p EXCEPT ![p] = [node |-> {}, edge |-> {}]]
                            <7> DEFINE tmp_g == [g EXCEPT ![p] = g_p_p(g[p])] 
                            <7>1. g' = [g EXCEPT ![p] = g_p_m_owner(g[p])] \/  g' = [tmp_g EXCEPT ![p] = g_p_m_owner(tmp_g[p])] 
                                BY <1>4, <2>1, <3>4, <6>2 DEF  ReceiveMessage, ReceiveBCAST, TypeInvariant    
                            <7> QED BY <7>1, <6>2 DEF TypeInvariant
                        <6>3. CASE pi = p /\ pj # m.owner /\ pj = p /\ flag.abcast[p] # 0
                            BY <6>3, <1>4, <2>1, <3>4 DEF  ReceiveMessage, ReceiveBCAST, TypeInvariant
                        <6> QED BY ONLY <4>1, <6>1, <6>2, <6>3
                    (* Servers can only be added to M *)    
                    <5>2. pj \in M[pi] => pj \in M'[pi]
                        <6>1. CASE pi # p 
                            BY <1>4, <2>1, <3>4, <6>1 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
                        <6>2. CASE pi = p
                            <7>1.  M'[p] = M[p] \cup {p, m.owner} \/ M'[p] = M[p] \cup {m.owner}
                                BY <1>4, <2>1, <3>4, <6>2 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
                            <7> QED BY <7>1, <6>2, <4>1
                        <6> QED BY ONLY <6>1, <6>2
                    <5> SUFFICES ASSUME PathsFromTo(RTD, pj, q) = {},
                                        pj \notin M'[pi] 
                                 PROVE PathsFromTo(RTD, pj, q)' = {}
                        BY <3>1, <3>3, <5>1, <5>2 DEF RTD, rtd_inv
                    <5> SUFFICES ASSUME PathsFromTo(RTD, pj, q)' # {}
                                 PROVE FALSE
                        OBVIOUS
                    (* Assume that there is an edge in RTD' that is not in RTD *)    
                    <5> SUFFICES ASSUME \E e \in rtd_edges' : e \notin rtd_edges
                                 PROVE FALSE
                        BY <3>3 DEF PathsFromTo, Path
                    <5>3. PICK e \in rtd_edges' : e \notin rtd_edges
                        OBVIOUS
                    (* This edge must be removed from RTD because it was never used *)    
                    <5>4. /\ e[2] \in F[pi][e[1]] /\ pj \notin M[pi]
                          /\ (e[2] \notin F'[pi][e[1]] \/ pj \in M'[pi]) 
                        BY <5>3 DEF rtd_edges
                    (* pj is added to M[pi] => rtd_inv(pi,pj,q)' *)
                    <5>5. pj \notin M[pi] /\ pj \in M'[pi] BY ONLY <3>1, <5>4 
                    <5> QED BY <5>5
                <4>2. CASE pi = p /\ pj = m.owner
                    <5>1. M'[p] = M[p] \cup {p, m.owner} \/ M'[p] = M[p] \cup {m.owner}
                        BY <1>4, <2>1, <3>4, <4>2 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
                    (* m.owner is added to M[p] => rtd_inv(p,m.owner,q)' *)
                    <5>2. pj \in M'[pi] BY ONLY <5>1, <4>2
                    <5> QED BY ONLY <5>2 DEF rtd_inv
                <4>3. CASE pi = p /\ pj # m.owner /\ pj = p /\ flag.abcast[p] = 0
                    <5>1. M'[p] = M[p] \cup {p, m.owner} 
                        BY <1>4, <2>1, <3>4, <4>3 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
                    (* p is added to M[p] => rtd_inv(p,p,q)' *)    
                    <5>2. pj \in M'[pi] BY ONLY <4>3, <5>1
                    <5> QED BY <5>2 DEF rtd_inv
                <4> QED BY ONLY <4>1, <4>2, <4>3
            <3>5. CASE ~ (flag.abcast[m.owner] = 1 /\ m.owner \notin M[p])
                <4>1. UNCHANGED <<M,g>> BY <1>4, <2>1, <3>5 DEF ReceiveMessage, ReceiveBCAST
                <4>2. PathsFromTo(RTD, pj, q) = PathsFromTo(RTD, pj, q)' 
                    <5>1. rtd_edges' = rtd_edges BY <4>1, <3>1, <3>3, <3>2 DEF DigraphType, rtd_edges
                    <5> QED BY <5>1, <3>3, <3>2 DEF PathsFromTo, Path    
                <4> QED BY <3>1, <3>3, <4>1, <4>2 DEF rtd_inv, RTD      
            <3> QED BY <3>4, <3>5            
        <2>2. CASE m.type = "FAIL"
            <3> m.owner \in Server /\ m.target \in Server  
                BY <1>4, <2>2, NextTypeInv DEF TypeInvariant, NetTypeInvariant, Message, NextTypeInv, Next
            (* M is unchanged *)
            <3>1. UNCHANGED <<M>> BY <1>4, <2>2 DEF ReceiveMessage
            <3> DEFINE RTD == ReconstructedTD(pi,pj)
            <3> /\ RTD \in DigraphType(Server) 
                /\ RTD' \in DigraphType(Server) 
                BY DEF DigraphType, ReconstructedTD    
            <3> HIDE DEF RTD
            <3> DEFINE all_rtd_edges == {e \in RTD.node \X RTD.node : F[pi][e[1]] # {} /\ e \in G.edge}
            <3> DEFINE rtd_edges == all_rtd_edges \ {e \in all_rtd_edges : e[2] \in F[pi][e[1]] /\ pj \notin M[pi]}
            <3> /\ RTD.edge = rtd_edges
                /\ RTD'.edge = rtd_edges' 
                BY DEF RTD, ReconstructedTD, TypeInvariant
            <3> HIDE DEF rtd_edges      
            <3>2. CASE m.owner \in F[p][m.target]
                <4>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' 
                    BY <1>4, <2>2, <3>2 DEF ReconstructedTD, ReceiveMessage, ReceiveFAIL 
                <4> QED BY <1>4, <2>2, <3>2, <4>1 DEF ReceiveMessage, ReceiveFAIL, rtd_inv
            <3>3. CASE m.owner \notin F[p][m.target] (* New failure notification *)
                <4> DEFINE pk == m.owner
                <4> DEFINE PruneAllFaulty(p_star, tg) == 
                                 IF \A srv \in tg.node : F[p][srv] # {} THEN [node |-> {}, edge |-> {}] ELSE tg
                <4> DEFINE g_p == [p_star \in Server |-> 
                                    IF m.target \notin g[p][p_star].node THEN g[p][p_star] 
                                    ELSE PruneAllFaulty(p_star, TrackingDigraph(p, p_star))']
                (* Definition of g' *)
                <4> g' = [g EXCEPT ![p] = g_p] 
                    BY <1>4, <2>2, <3>3 DEF ReceiveMessage, ReceiveFAIL
                <4> HIDE DEF PruneAllFaulty, g_p
                (* Definition of F' *)
                <4> F' = [F EXCEPT ![p][m.target] = F[p][m.target] \cup {m.owner}]
                    BY <1>4, <2>2, <3>3 DEF ReceiveMessage, ReceiveFAIL      
                <4>1. CASE pi # p
                    (* pi # p => rtd_inv is unchanged *)
                    <5>1. UNCHANGED <<g[pi]>> BY <4>1 DEF TypeInvariant
                    <5>2. UNCHANGED <<F[pi]>>
                        BY <1>4, <2>2, <3>3, <4>1 DEF ReceiveMessage, ReceiveFAIL, TypeInvariant
                    <5>3. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)'
                        BY <5>1, <5>2, <3>1 DEF ReconstructedTD, TypeInvariant
                    <5> QED BY <5>1, <5>2, <3>1, <5>3 DEF rtd_inv
                <4>2. CASE pi = p
                    <5>1. \A srv \in Server : srv # pi => UNCHANGED <<F[srv]>> 
                        BY <4>2 DEF TypeInvariant
                    <5>2. F'[pi][m.target] = F[pi][m.target] \cup {m.owner}
                        BY <4>2 DEF TypeInvariant
                    <5>3. \A srv \in Server : srv # m.target => UNCHANGED <<F[pi][srv]>>
                        BY <4>2 DEF TypeInvariant
                    <5>4. g'[pi][pj] = g_p[pj] BY <4>2 DEF TypeInvariant
                    <5>5. CASE q = m.target
                        (* q = m.target => F'[pi][q] # {} => rtd_inv' *)
                        BY <5>5, <5>2 DEF rtd_inv
                    <5>6. CASE q # m.target
                        (* F[pi][q] is unchanged *)
                        <6>1. UNCHANGED <<F[pi][q]>>
                            BY <5>6, <5>3
                        <6>2. CASE q \notin RTD'.node \/ q \in g'[pi][pj].node
                            (* FALSE => X is always true regardless of X *)
                            BY <6>2 DEF rtd_inv, RTD
                        <6>3. CASE q \in RTD'.node /\ q \notin g'[pi][pj].node                                   
                            <8>1. CASE \/ pj \in M'[pi]
                                       \/ F'[pi][q] # {}
                                       \/ PathsFromTo(RTD', pj, q) = {}
                                BY <8>1 DEF RTD, rtd_inv
                            <8>2. CASE /\ pj \notin M'[pi]
                                       /\ F'[pi][q] = {}
                                       /\ PathsFromTo(RTD', pj, q) # {}
                                (* Choose an arbitrary path from pj to q in RTD' *)        
                                <9>2. PICK P \in PathsFromTo(RTD', pj, q) : TRUE
                                    BY ONLY <8>2     
                                (* -> every node on P is a Server *)    
                                <9>3. \A k \in 1..Len(P) : P[k] \in Server    
                                    BY <9>2 DEF PathsFromTo, Path, DigraphType
                                (* -> every edge on P is a from rtd_edges' *)    
                                <9>4. \A k \in 1..Len(P)-1 : <<P[k],P[k+1]>> \in rtd_edges'
                                    BY <9>2 DEF PathsFromTo, Path
                                (* -> every node on P (except q) is faulty *)       
                                <9>5. \A k \in 1..Len(P)-1 : F'[pi][P[k]] # {}
                                    BY <9>4 DEF rtd_edges
                                <9> DEFINE successor(srv) == Successors(G, srv) \ F[pi][srv]
                                <9> DEFINE edges1 == {e \in Server \X Server : F[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
                                <9> DEFINE tg_nodes == {srv \in Server : 
                                                AreConnectedViaFailures(pj, srv, [node |-> Server, edge |-> edges1], F[pi])}
                                <9>6. /\ TrackingDigraph(pi, pj)'.node = tg_nodes'
                                      /\ TrackingDigraph(pi, pj).node = tg_nodes
                                    BY DEF TrackingDigraph
                                <9> HIDE DEF tg_nodes  
                                (* -> every node on P is also in TrackingDigraph(pi, pj)'.node *)
                                <9>7. \A k \in 1..Len(P) : P[k] \in TrackingDigraph(pi, pj)'.node
                                    <10>1. ASSUME NEW k \in 1..Len(P)-1
                                           PROVE <<P[k],P[k+1]>> \in edges1'
                                        <11>1. F'[pi][P[k]] # {} BY <9>4 DEF rtd_edges    
                                        <11>2. P[k+1] \in Successors(G, P[k])
                                            BY ONLY <9>3, <9>4 DEF Successors, rtd_edges, G
                                        <11>3. P[k+1] \notin F'[pi][P[k]]
                                            BY ONLY <8>2, <9>4 DEF rtd_edges           
                                        <11> QED BY ONLY <9>3, <11>1, <11>2, <11>3
                                    <10>2. P \in Path([node |-> Server, edge |-> edges1'])
                                        BY ONLY <9>2, <10>1 DEF PathsFromTo, Path  
                                    <10> SUFFICES ASSUME NEW k \in 1..Len(P)
                                                 PROVE AreConnectedViaFailures(pj, P[k], [node |-> Server, edge |-> edges1], F[pi])'
                                        BY <9>6, <9>3 DEF tg_nodes  
                                    <10> DEFINE part_P == SubSeq(P,1,k)
                                    <10> HIDE DEF part_P
                                    <10>3. part_P \in Path([node |-> Server, edge |-> edges1'])
                                        BY ONLY <10>2 DEF Path, part_P
                                    <10>4. part_P[1] = pj BY ONLY <9>2 DEF part_P, PathsFromTo
                                    <10>5. part_P[Len(part_P)] = P[k] BY ONLY <9>2 DEF part_P, PathsFromTo
                                    <10>6. \A l \in 1..Len(part_P)-1 : F'[pi][part_P[l]] # {}
                                        BY ONLY <9>5 DEF part_P              
                                    <10> QED BY ONLY <10>3, <10>4, <10>5, <10>6 DEF AreConnectedViaFailures
                                <9>8. CASE m.target \in g[pi][pj].node
                                    (* Show that g'[pi][pj] = TD'(pi,pj) *)
                                    <10>1. g'[pi][pj] = PruneAllFaulty(pj, TrackingDigraph(pi, pj))'
                                        BY <4>2, <5>4, <9>8 DEF g_p
                                    <10>2. q \in TrackingDigraph(pi, pj)'.node 
                                        BY ONLY <9>7, <9>2 DEF PathsFromTo, Path   
                                    <10>3. g'[pi][pj] = TrackingDigraph(pi, pj)'
                                        BY ONLY <4>2, <8>2, <10>1, <10>2 DEF PruneAllFaulty 
                                    (* Since q \in TD'[pi][pj] = g'[pi][pj] => contradiction *)  
                                    <10> QED BY ONLY <6>3, <10>2, <10>3      
                                <9>9. CASE m.target \notin g[pi][pj].node
                                    (* g[pi][pj] is unchanged *)
                                    <10>1. UNCHANGED <<g[pi][pj]>> 
                                        BY <4>2, <5>4, <9>9 DEF g_p
                                    (* use Possible Tracking Digraphs invariant *)
                                    <10>2. \/ (g'[pi][pj] = [node |-> {pj}, edge |-> {}] /\ F[pi][pj] = {})
                                           \/ g'[pi][pj] = [node |-> {}, edge |-> {}]
                                           \/ g'[pi][pj] = TrackingDigraph(pi,pj)  
                                        BY <10>1 DEF PTD      
                                    <10>3. CASE g'[pi][pj] = [node |-> {pj}, edge |-> {}] /\ F[pi][pj] = {}
                                        (* PTD option #1 *)
                                        <11>1. pj # q BY ONLY <6>3, <10>3
                                        <11>2. pj # m.target BY ONLY <9>9, <10>1, <10>3
                                        <11>3. F'[pi][pj] = {} BY ONLY <11>2, <5>3, <10>3 
                                        <11>4. Len(P) > 1 BY ONLY <11>1, <9>2 DEF PathsFromTo, Path
                                        <11>5. F'[pi][pj] # {} BY ONLY <9>5, <11>4 DEF PathsFromTo
                                        (* Contradiction *)
                                        <11> QED BY ONLY <11>3, <11>5
                                    <10>4. CASE g'[pi][pj] = [node |-> {}, edge |-> {}]
                                        (* PTD option #2 *)
                                        (* use Empty Tracking Digraph invariant *)
                                        <11>1. \/ pj \in M[pi]
                                               \/ \A srv \in TrackingDigraph(pi, pj).node : F[pi][srv] # {}
                                            BY <10>1, <10>4 DEF ETD    
                                        <11>2. \A srv \in TrackingDigraph(pi, pj).node : F[pi][srv] # {}
                                            BY ONLY <8>2, <3>1, <11>1    
                                        (* All servers in TrackingDigraph(pi, pj) are faulty. 
                                           Show that TrackingDigraph(pi, pj) = TrackingDigraph(pi, pj)'. *)    
                                        <11>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges1], F[pi])'
                                            <12>1. q \in TrackingDigraph(pi, pj)'.node 
                                                BY ONLY <9>7, <9>2 DEF PathsFromTo, Path
                                            <12> QED BY ONLY <9>6, <12>1 DEF tg_nodes
                                        <11>4. pj # q
                                            <12>1. SUFFICES ASSUME pj = q 
                                                            PROVE FALSE
                                                OBVIOUS
                                            <12>2. q \in TrackingDigraph(pi, pj).node 
                                                BY ONLY <9>6, <12>1 DEF tg_nodes, AreConnectedViaFailures
                                            <12>3. F'[pi][q] # {}
                                                BY ONLY <12>2, <11>2, <5>6, <5>3  
                                            <12> QED BY ONLY <8>2, <12>3
                                        <11>5. PICK tdP \in Path([node |-> Server, edge |-> edges1']) : 
                                                          /\ (tdP[1] = pj) 
                                                          /\ (tdP[Len(tdP)] = q) 
                                                          /\ (\A i \in 1..Len(tdP)-1 : F'[pi][tdP[i]] # {})
                                            BY <11>3, <11>4 DEF AreConnectedViaFailures
                                        <11>6. \A k \in 1..Len(tdP)-1 : <<tdP[k],tdP[k+1]>> \in edges1
                                            <12>1. SUFFICES ASSUME \E k \in 1..Len(tdP)-1 : <<tdP[k],tdP[k+1]>> \notin edges1
                                                            PROVE FALSE
                                                OBVIOUS
                                            <12>2. PICK k \in 1..Len(tdP)-1 : /\ <<tdP[k],tdP[k+1]>> \notin edges1   
                                                                              /\ \A l \in 1..k-1 : <<tdP[l],tdP[l+1]>> \in edges1
                                                <13> DEFINE Prop(k) ==  IF k \in 1..Len(tdP)-1 
                                                                        THEN <<tdP[k],tdP[k+1]>> \notin edges1 
                                                                        ELSE FALSE
                                                <13> HIDE DEF Prop
                                                <13>1. \E k \in 1..Len(tdP)-1 : Prop(k) BY ONLY <12>1 DEF Prop  
                                                <13>2. \E k \in Nat : Prop(k) BY ONLY <13>1
                                                <13>3. \E k \in Nat : Prop(k) /\ \A l \in 0..k-1 : ~Prop(l) 
                                                    BY ONLY <13>2, SmallestNatural
                                                <13> QED BY ONLY <13>3, <13>1 DEF Prop
                                            <12>3. tdP[k] \in Server /\ tdP[k+1] \in Server BY ONLY <11>5 DEF Path
                                            <12>4. F[pi][tdP[k]] = {} \/  tdP[k+1] \in F[pi][tdP[k]]
                                                BY ONLY <12>2, <12>3, <11>5 DEF Successors, Path
                                            <12>5. F'[pi][tdP[k]] # {} BY ONLY <11>5 DEF Path
                                            <12>6. CASE F[pi][tdP[k]] = {}
                                                <13> DEFINE part_tdP == SubSeq(tdP,1,k)
                                                <13> HIDE DEF part_tdP
                                                <13>1. part_tdP \in Path([node |-> Server, edge |-> edges1]) 
                                                    BY ONLY <11>5, <12>2 DEF Path, part_tdP
                                                <13>2. \A l \in 1..k : part_tdP[l] = tdP[l] BY ONLY DEF part_tdP    
                                                <13>3. part_tdP[1] = pj BY ONLY <13>2, <11>5
                                                <13>4. part_tdP[Len(part_tdP)] = tdP[k] BY ONLY <13>3 DEF part_tdP
                                                <13>5. \A l \in 1..Len(part_tdP)-1 : F[pi][part_tdP[l]] # {} 
                                                    BY ONLY <12>2 DEF part_tdP
                                                <13>6. AreConnectedViaFailures(pj, tdP[k], [node |-> Server, edge |-> edges1], F[pi])
                                                   BY ONLY <13>1, <13>3, <13>4, <13>5 DEF AreConnectedViaFailures
                                                <13>7. tdP[k] \in TrackingDigraph(pi, pj).node 
                                                    BY ONLY <13>6, <9>6, <11>5 DEF tg_nodes, Path   
                                                <13> QED BY ONLY <12>6, <13>7, <11>2
                                            <12>7. CASE tdP[k+1] \in F[pi][tdP[k]]
                                                <13>1. tdP[k+1] \in F'[pi][tdP[k]]
                                                    BY ONLY <12>7, <5>2, <5>3, <11>5 DEF Path
                                                <13>2. <<tdP[k],tdP[k+1]>> \notin edges1'
                                                    BY ONLY <13>1    
                                                <13> QED BY ONLY <13>2, <11>5 DEF Path
                                            <12> QED BY ONLY <12>4, <12>6, <12>7 
                                        <11>7. \A k \in 1..Len(tdP)-1 : F[pi][tdP[k]] # {} BY ONLY <11>6
                                        <11>8. tdP \in Path([node |-> Server, edge |-> edges1])  
                                            BY ONLY <11>5, <11>6 DEF Path
                                        <11>9. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges1], F[pi])
                                            BY ONLY <11>5, <11>7, <11>8 DEF AreConnectedViaFailures
                                        <11>10. q \in TrackingDigraph(pi, pj).node 
                                            BY ONLY <11>9, <9>6 DEF tg_nodes
                                        (* F[pi][q] # {};  F'[pi][q] = {}; unchanged F[pi][q] => contradiction *)    
                                        <11> QED BY ONLY <8>2, <11>10, <11>2, <9>7, <5>6, <5>3
                                    <10>5. CASE g'[pi][pj] = TrackingDigraph(pi,pj)
                                        (* PTD option #3 *)
                                        (* q \in TD(pi,pj)' *) 
                                        <11>1. q \in TrackingDigraph(pi,pj)'.node
                                            BY ONLY <9>7, <9>2 DEF PathsFromTo, Path
                                        <11>2. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges1], F[pi])'
                                            BY ONLY <11>1, <9>6 DEF tg_nodes
                                        (* q \notin TD(pi,pj) *)    
                                        <11>3. q \notin TrackingDigraph(pi,pj).node
                                            BY ONLY <10>5, <6>3
                                        <11>4. pj # q 
                                            BY ONLY <11>3, TDConstruction DEF TDHasRoot, G
                                        (* pick path in TD' from pj to q *)    
                                        <11>5. PICK tdP \in Path([node |-> Server, edge |-> edges1']) : 
                                                          /\ (tdP[1] = pj) 
                                                          /\ (tdP[Len(tdP)] = q) 
                                                          /\ (\A i \in 1..Len(tdP)-1 : F'[pi][tdP[i]] # {})
                                            BY ONLY <11>4, <11>2 DEF AreConnectedViaFailures
                                        (* there is an edge on the path that is not in TD *)    
                                        <11>6. \E k \in 1..Len(tdP)-1 : <<tdP[k],tdP[k+1]>> \notin edges1
                                            <12>1. SUFFICES ASSUME \A k \in 1..Len(tdP)-1 : <<tdP[k],tdP[k+1]>> \in edges1
                                                          PROVE FALSE
                                                OBVIOUS
                                            <12>2. \A i \in 1..Len(tdP)-1 : F[pi][tdP[i]] # {}
                                                BY ONLY <12>1
                                            <12>3. AreConnectedViaFailures(pj, q, [node |-> Server, edge |-> edges1], F[pi]) 
                                                BY ONLY <11>5, <12>1, <12>2 DEF Path, AreConnectedViaFailures   
                                            <12>4. q \in TrackingDigraph(pi,pj).node
                                                BY ONLY <12>3, <9>6 DEF tg_nodes 
                                            <12> QED BY ONLY <11>3, <12>4
                                        (* let e be the first such edge on the path *)    
                                        <11>7. PICK k \in 1..Len(tdP)-1 : /\ <<tdP[k],tdP[k+1]>> \notin edges1   
                                                                          /\ \A l \in 1..k-1 : <<tdP[l],tdP[l+1]>> \in edges1
                                            <12> DEFINE Prop(k) ==  IF k \in 1..Len(tdP)-1 
                                                                    THEN <<tdP[k],tdP[k+1]>> \notin edges1 
                                                                    ELSE FALSE
                                            <12> HIDE DEF Prop
                                            <12>1. \E k \in 1..Len(tdP)-1 : Prop(k) BY ONLY <11>6 DEF Prop  
                                            <12>2. \E k \in Nat : Prop(k) BY ONLY <12>1
                                            <12>3. \E k \in Nat : Prop(k) /\ \A l \in 0..k-1 : ~Prop(l) 
                                                BY ONLY <12>2, SmallestNatural
                                            <12> QED BY ONLY <12>3, <12>1 DEF Prop        
                                        <11>8. tdP[k] \in Server /\ tdP[k+1] \in Server BY ONLY <11>5 DEF Path
                                        (* either e1 is non-faulty or e2 detected its failure *)
                                        <11>9. F[pi][tdP[k]] = {} \/  tdP[k+1] \in F[pi][tdP[k]]
                                            BY ONLY <11>7, <11>8, <11>5 DEF Successors, Path
                                        (* e1 is faulty afterwards *)        
                                        <11>10. F'[pi][tdP[k]] # {} BY ONLY <11>5 DEF Path
                                        (* m.target \notin TD *)
                                        <11>11. m.target \notin TrackingDigraph(pi,pj).node
                                            BY ONLY <10>5, <9>9, <10>1
                                        <11>12. CASE F[pi][tdP[k]] = {} (* e1 is non-faulty *)
                                            (* e1 is m.target (only F modification) *)
                                            <12>1. tdP[k] = m.target BY ONLY <11>8, <11>10, <11>12, <5>2, <5>3
                                            (* let's consider the prefix of the path until e1 *)
                                            <12> DEFINE part_tdP == SubSeq(tdP,1,k)
                                            <12> HIDE DEF part_tdP
                                            <12>2. part_tdP \in Path([node |-> Server, edge |-> edges1])
                                                BY ONLY <11>5, <11>7 DEF Path, part_tdP
                                            <12>3. part_tdP[1] = pj BY ONLY <11>5 DEF part_tdP
                                            <12>4. part_tdP[Len(part_tdP)] = tdP[k] BY ONLY <11>5 DEF part_tdP
                                            <12>5. \A l \in 1..Len(part_tdP)-1 : F[pi][part_tdP[l]] # {} 
                                                BY ONLY <11>7 DEF part_tdP   
                                            <12>6. AreConnectedViaFailures(pj, tdP[k], [node |-> Server, edge |-> edges1], F[pi])
                                                BY ONLY <12>2, <12>3, <12>4, <12>5 DEF AreConnectedViaFailures
                                            (* e1 \in TD(pi,pj) *)   
                                            <12>7. tdP[k] \in TrackingDigraph(pi, pj).node 
                                                BY ONLY <12>6, <9>6, <11>5 DEF tg_nodes, Path     
                                            (* e1 \in TD; e1=m.target; e1 \notin TD => contradiction *)     
                                            <12> QED BY ONLY <12>7, <12>1, <11>11
                                        <11>13.CASE tdP[k+1] \in F[pi][tdP[k]] (* e2 detected e1's failure *)
                                            <12>1. tdP[k+1] \in F'[pi][tdP[k]]
                                                BY ONLY <11>13, <5>2, <5>3 DEF Path
                                            <12>2. <<tdP[k],tdP[k+1]>> \notin edges1'
                                                BY ONLY <12>1    
                                            <12> QED BY ONLY <12>2, <11>5 DEF Path      
                                        <11> QED BY ONLY <11>9, <11>12, <11>13                 
                                    <10> QED BY ONLY <10>2, <10>3, <10>4, <10>5
                                <9> QED BY ONLY <9>8, <9>9
                            <8> QED BY ONLY <8>1, <8>2                            
                        <6> QED BY <6>2, <6>3                   
                    <5> QED BY ONLY <5>5, <5>6
                <4> QED BY ONLY <4>1, <4>2
            <3> QED BY ONLY <3>2, <3>3
        <2>3. CASE m.type # "BCAST" /\ m.type # "FAIL"
            <3>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' 
                BY <1>4, <2>3 DEF ReceiveMessage, ReconstructedTD
            <3> QED BY <1>4, <2>3, <3>1 DEF ReceiveMessage, rtd_inv
        <2> QED BY <2>1, <2>2, <2>3
    (* Prove that RTDInvariant is preserved by Adeliver(p) *)
    <1>5. ASSUME RTDInvariant, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE RTDInvariant'
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>5 DEF RTDInvariant, rtd_inv  
        <2>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' BY <1>5 DEF Adeliver, ReconstructedTD
        <2> QED BY <1>5, <2>1 DEF Adeliver, rtd_inv
    (* Prove that RTDInvariant is preserved by Fail(p) *)
    <1>6. ASSUME RTDInvariant, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE RTDInvariant'
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>6 DEF RTDInvariant, rtd_inv
        <2>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' BY <1>6 DEF Fail, ReconstructedTD
        <2> QED BY <1>6, <2>1 DEF Fail, rtd_inv
    (* Prove that RTDInvariant is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME RTDInvariant, 
                 NEW pf \in Server, 
                 NEW pd \in Server,
                 DetectFailure(pf,pd) 
          PROVE RTDInvariant'
        <2> SUFFICES ASSUME NEW pi \in Server,
                            NEW pj \in Server,
                            NEW q \in Server,
                            rtd_inv(pi,pj,q)
                     PROVE rtd_inv(pi,pj,q)'
            BY <1>7 DEF RTDInvariant, rtd_inv
        <2>1. ReconstructedTD(pi, pj) = ReconstructedTD(pi, pj)' BY <1>7 DEF DetectFailure, ReconstructedTD
        <2> QED BY <1>7, <2>1 DEF DetectFailure, rtd_inv
    <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
    
(* Prove that RTDInvariant is preserved by the specification Spec *) 
THEOREM RTDInv == Spec => []RTDInvariant             
    (* Prove stuttering step *) 
    <1>1. RTDInvariant /\ UNCHANGED vars => RTDInvariant' 
        BY DEF RTDInvariant, vars, ReconstructedTD
    (* Prove TypeInvariant *) 
    <1> Spec => TypeInvariant BY PTL, TypeInv
    (* Prove PTD *) 
    <1> Spec => PTD BY PTL, PTDInv
    (* Prove ETD *) 
    <1> Spec => ETD BY PTL, ETDInv
    (* Use InitRTDInv and NextRTDInv *)
    <1>2. /\ Spec 
          /\ TypeInvariant
          /\ PTD 
          /\ ETD
          => []RTDInvariant
        <2> SUFFICES ASSUME Spec, 
                            TypeInvariant,
                            PTD,
                            ETD
                     PROVE []RTDInvariant
            OBVIOUS
        <2> QED BY PTL, InitRTDInv, NextRTDInv, <1>1 DEF Spec    
    <1> QED BY <1>2
    
=============================================================================