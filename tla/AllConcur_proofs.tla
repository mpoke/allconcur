(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE AllConcur_proofs ---------------------
(***************************************************************************
 * Safety & Liveness Properties for AllConcur
 ***************************************************************************)

EXTENDS AllConcur, NaturalsInduction, SequenceTheorems, FiniteSetTheorems, 
        ExactSeqs_proofs, TypeInvariant_proofs, 
        FD_proofs, ReconstructedTD, TLAPS

-----------------------------------------------------------------------------
(* AXIOMS *)

(* The digraph G has connectivity larger than f *)
AXIOM ReliableDigraph == 
    \A pi,pj \in Server : pi # pj => Cardinality(NodeDisjPathsFromTo(G, pi, pj)) > f
       
-----------------------------------------------------------------------------
(* Helping theorems *)

THEOREM TerminateTDEmpty == 
    ASSUME NEW p \in Server,
           flag.done[p] = 1 \/ flag'.done[p] = 1
    PROVE \A q \in Server : g[p][q].node = {}
  OMITTED
  
(* If a server p receives a message m, then there is a path in G from m's owner to p 
   s.t. every server on the path has received m from its predecessor on the path.  *)  
THEOREM MessagePath == 
    \A p,pi \in Server : p \in M[pi] => \E P \in PathsFromTo(G,p,pi) :
                            \* any server on the path has the message 
                            /\ \A k \in 1..Len(P) : p \in M[P[k]]   
                            \* as well as any other server that receives a failure notification 
                            \* corresponding to an edge on the path 
                            /\ \A pj \in Server : ((\E k \in 1..Len(P)-1 : P[k+1] \in F[pj][P[k]]) => p \in M[pj])
    OMITTED

-----------------------------------------------------------------------------
(***************************************************************************
 * Safety Properties
 * Integrity & Total order (Set agreement)
 ***************************************************************************)

(* Integrity
       
Integrity == \* PROPERTY: Integrity
    \A p \in Server : (flag.nonFaulty[p] = 1 => (\A m \in M[p] : flag.abcast[m] = 1))
    \* Note that "a server A-delivers m at most once" is ensured by constuction (M[p] is a set)
*)
THEOREM InitIntegrityInv == Init => Integrity             
    BY DEF Init, Integrity
       
THEOREM NextIntegrityInv == TypeInvariant /\ Integrity /\ Next => Integrity'
    <1> SUFFICES ASSUME TypeInvariant
                 PROVE Integrity /\ Next => Integrity'
        OBVIOUS
    <1>1. SUFFICES /\ (Integrity /\ \E p \in Server : Abcast(p)) => Integrity'
                   /\ (Integrity /\ \E p \in Server : TXMessage(p)) => Integrity'
                   /\ (Integrity /\ \E p \in Server : ReceiveMessage(p)) => Integrity'
                   /\ (Integrity /\ \E p \in Server : Adeliver(p)) => Integrity'
                   /\ (Integrity /\ \E p \in Server : Fail(p)) => Integrity'
                   /\ (Integrity /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => Integrity'
        BY DEF Next
    (* Prove that Integrity is preserved by Abcast(p) *)
    <1>2. ASSUME Integrity, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE Integrity'
        (* Sufficient to prove the property for a given server q *)  
        <2> SUFFICES ASSUME NEW q \in Server
                     PROVE (flag.nonFaulty[q] = 1 => (\A m \in M[q] : flag.abcast[m] = 1))'
            BY DEF Integrity  
        <2>1. UNCHANGED <<flag.nonFaulty[q]>> 
            BY Abcast(p) DEF Abcast, TypeInvariant
        (* Sufficient to prove that a message m known by a non-faulty servers q was A-broadcast *)
        <2> SUFFICES ASSUME flag'.nonFaulty[q] = 1,
                            NEW m \in M'[q]
                     PROVE flag'.abcast[m] = 1
            OBVIOUS
        (* m can be either previously known or the message A-broadcast by p *)    
        <2>2. m \in M[q] \/ m = p BY Abcast(p) DEF Abcast, TypeInvariant
        <2>3. CASE m = p
            <3>1. flag'.abcast[p] = 1 BY Abcast(p) DEF Abcast, TypeInvariant
            <3> QED BY <2>3, <3>1
        <2>4. CASE m # p
            <3>1. m \in M[q] BY <2>4, <2>2
            <3>2. \A msg \in M[q] : flag.abcast[msg] = 1 BY <2>1, Integrity DEF Integrity
            <3>3. UNCHANGED <<flag.abcast[m]>> BY <2>4, Abcast(p) DEF Abcast, TypeInvariant
            <3> QED BY <3>1, <3>2, <3>3 
        <2> QED BY <2>3, <2>4
    (* Prove that Integrity is preserved by TXMessage(p) *)      
    <1>3. ASSUME Integrity, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE Integrity'
          BY <1>3 DEF Integrity, TXMessage
    (* Prove that Integrity is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME Integrity, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE Integrity'
        (* Sufficient to prove the property for a given server q *)  
        <2> SUFFICES ASSUME NEW q \in Server
                     PROVE (flag.nonFaulty[q] = 1 => (\A m \in M[q] : flag.abcast[m] = 1))'
            BY DEF Integrity
        <2>1. CASE recvMsg'.type = "BCAST"
            <3> DEFINE m == recvMsg'
            <3> m \in Message 
                BY <1>4 DEF ReceiveMessage, DeliverMessage, TypeInvariant, NetTypeInvariant
            <3> SUFFICES ASSUME ReceiveBCAST(p, m)
                         PROVE (flag.nonFaulty[q] = 1 => (\A msg \in M[q] : flag.abcast[msg] = 1))'
                BY <1>4, <2>1 DEF ReceiveMessage
            <3>1. CASE flag.abcast[m.owner] = 1 /\ m.owner \notin M[p] 
                <4>1. UNCHANGED <<flag.nonFaulty[q]>> 
                    BY DEF ReceiveBCAST, TypeInvariant
                <4> SUFFICES ASSUME flag'.nonFaulty[q] = 1,
                                    NEW msg \in M'[q]
                             PROVE flag'.abcast[msg] = 1
                    OBVIOUS    
                <4>2. CASE flag.abcast[p] = 0 
                    <5>1.msg \in M[q] \/ msg = p \/ msg = m.owner
                        BY <3>1, <4>2 DEF ReceiveBCAST, TypeInvariant            
                    <5>2. \A message \in M[q] \cup {m.owner} \cup {p}: flag'.abcast[message] = 1
                        <6>1. flag' = [flag EXCEPT !.abcast[p] = 1] BY <3>1, <4>2 DEF ReceiveBCAST
                        <6>2. \A srv \in Server : srv # p => UNCHANGED <<flag.abcast[srv]>>
                            BY <6>1 DEF TypeInvariant 
                        <6>3. flag'.abcast[p] = 1 BY <6>1 DEF TypeInvariant
                        <6>4. M[q] \cup {m.owner} \subseteq Server BY DEF TypeInvariant, Message
                        <6>5. \A message \in M[q] \cup {m.owner} : flag.abcast[message] = 1 
                            BY <3>1, <4>1, Integrity DEF Integrity 
                        <6> QED BY <6>2, <6>3, <6>4, <6>5
                    <5> QED BY <5>1, <5>2    
                <4>3. CASE flag.abcast[p] # 0
                    <5>1. msg \in M[q] \/ msg = m.owner 
                        BY <3>1, <4>3 DEF ReceiveBCAST, TypeInvariant
                    <5>2. UNCHANGED <<flag.abcast[msg]>> 
                        BY <4>3 DEF ReceiveBCAST, TypeInvariant
                    <5>3. \A message \in M[q] : flag.abcast[message] = 1 
                        BY <4>1, Integrity DEF Integrity          
                    <5> QED BY <3>1, <5>1, <5>2, <5>3 
                <4> QED BY <4>2, <4>3
            <3>2. CASE ~ (flag.abcast[m.owner] = 1 /\ m.owner \notin M[p])
                BY <1>4, <3>2 DEF ReceiveBCAST, Integrity
            <3> QED BY <3>1, <3>2     
        <2>2. CASE recvMsg'.type = "FAIL"
            BY <1>4, <2>2 DEF Integrity, ReceiveMessage
        <2>3. CASE (recvMsg'.type # "BCAST" /\ recvMsg'.type # "FAIL")
            BY <1>4, <2>3 DEF Integrity, ReceiveMessage
        <2> QED BY <2>1, <2>2, <2>3          
    (* Prove that Integrity is preserved by Adeliver(p) *)
    <1>5. ASSUME Integrity, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE Integrity'
        BY <1>5 DEF Integrity, Adeliver                 
    (* Prove that Integrity is preserved by Fail(p) *)
    <1>6. ASSUME Integrity, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE Integrity'  
        <2> SUFFICES ASSUME NEW q \in Server
                     PROVE (flag.nonFaulty[q] = 1 => (\A m \in M[q] : flag.abcast[m] = 1))'
            BY DEF Integrity    
        <2>1. CASE flag'.nonFaulty[q] # 1
            BY <2>1    
        <2>2. CASE flag'.nonFaulty[q] = 1
            <3> SUFFICES UNCHANGED <<flag.nonFaulty[q]>> 
                BY Integrity, Fail(p) DEF Fail, Integrity
            <3>3. CASE q # p 
                BY <3>3, <2>2, Fail(p) DEF Fail, TypeInvariant  
            <3>4. CASE q = p 
                BY <2>2, <3>4, Fail(p) DEF Fail 
            <3> QED BY <3>3, <3>4            
        <2> QED BY <2>1, <2>2          
    (* Prove that Integrity is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME Integrity, 
                 NEW pj \in Server, 
                 NEW pk \in Server,
                 DetectFailure(pj,pk) 
          PROVE Integrity'
           BY <1>7 DEF Integrity, DetectFailure
    <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7

(* Prove that the integrity invariant is preserved by the specification Spec *) 
THEOREM IntegrityInv == Spec => []Integrity             
    (* Prove stuttering step *) 
    <1>1. Integrity /\ UNCHANGED vars => Integrity' 
        BY DEF Integrity, vars
    (* Prove TypeInvariant *) 
    <1>2. Spec => TypeInvariant BY PTL, TypeInv
    (* Use InitIntegrityInv and NextIntegrityInv *)
    <1>3. Spec /\ TypeInvariant => []Integrity
        <2> SUFFICES ASSUME Spec, TypeInvariant 
                     PROVE []Integrity
            OBVIOUS
        <2> QED BY PTL, InitIntegrityInv, NextIntegrityInv, <1>1 DEF Spec    
    <1> QED BY <1>2, <1>3  
    
-----------------------------------------------------------------------------
(* SetAgreement

SetAgreement == \* PROPERTY: SetAgreement => Total order
    \A p,q \in Server : ( /\ (flag.nonFaulty[p] = 1 /\ flag.done[p] = 1)
                          /\ (flag.nonFaulty[q] = 1 /\ flag.done[q] = 1) ) => M[p] = M[q]
*)
THEOREM InitSetAgreementInv == Init => SetAgreement
    BY DEF Init, SetAgreement

THEOREM NextSetAgreementInv == /\ TypeInvariant
                               /\ FDAccuracy
                               /\ SetAgreement
                               /\ RTDInvariant 
                               /\ Next 
                               => SetAgreement'
    <1> SUFFICES ASSUME /\ TypeInvariant 
                        /\ FDAccuracy
                        /\ RTDInvariant
                 PROVE SetAgreement /\ Next => SetAgreement'
        OBVIOUS
    <1>1. SUFFICES /\ (SetAgreement /\ \E p \in Server : Abcast(p)) => SetAgreement'
                   /\ (SetAgreement /\ \E p \in Server : TXMessage(p)) => SetAgreement'
                   /\ (SetAgreement /\ \E p \in Server : ReceiveMessage(p)) => SetAgreement'
                   /\ (SetAgreement /\ \E p \in Server : Adeliver(p)) => SetAgreement'
                   /\ (SetAgreement /\ \E p \in Server : Fail(p)) => SetAgreement'
                   /\ (SetAgreement /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => SetAgreement'
        BY DEF Next
    <1> DEFINE set_agreement(p,q) == ( /\ (flag.nonFaulty[p] = 1 /\ flag.done[p] = 1)
                                       /\ (flag.nonFaulty[q] = 1 /\ flag.done[q] = 1) ) => M[p] = M[q]
    (* Clearly SetAgreement holds if the two servers are the same; also, the order doesn't matter *)
    <1>t. \A p, q \in Server : /\ p = q => set_agreement(p,q)'
                             /\ set_agreement(p,q)' <=> set_agreement(q,p)'
        OBVIOUS
    (* Prove that SetAgreement is preserved by Abcast(p) *)
    <1>2. ASSUME SetAgreement, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE SetAgreement'
        <2>1. UNCHANGED <<flag.done, flag.nonFaulty>> BY <1>2 DEF Abcast
        <2>2. \A q \in Server : q # p => UNCHANGED <<M[q]>>
            BY <1>2 DEF Abcast, TypeInvariant
        <2>3. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2)'
            <3>1. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2) = set_agreement(p1,p2)'
                BY <1>2, <2>1, <2>2 DEF SetAgreement
            <3> QED BY <1>2, <3>1 DEF SetAgreement    
        <2> SUFFICES ASSUME NEW q \in Server,  q#p
                      PROVE set_agreement(p,q)'
            BY <1>t, <2>3 DEF SetAgreement
        <2>4. flag'.done[p] = 0 BY <1>2, <2>1 DEF Abcast
        <2> QED BY <2>4      
    (* Prove that SetAgreement is preserved by TXMessage(p) *)      
    <1>3. ASSUME SetAgreement, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE SetAgreement'
        BY <1>3 DEF SetAgreement, TXMessage
    (* Prove that SetAgreement is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME SetAgreement, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE SetAgreement'
        <2>1.CASE recvMsg'.type = "BCAST"
            <3> DEFINE m == recvMsg'
            <3> m \in Message 
                BY <1>4 DEF ReceiveMessage, DeliverMessage, TypeInvariant, NetTypeInvariant
            <3>1. UNCHANGED <<flag.nonFaulty, flag.done>> 
                BY <1>4, <2>1 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
            <3>2. \A q \in Server : q # p => UNCHANGED <<M[q]>>
                BY <1>4 DEF ReceiveMessage, ReceiveBCAST, TypeInvariant
            <3>3. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2)'
                <4>1. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2) = set_agreement(p1,p2)'
                    BY <1>4, <3>1, <3>2 DEF SetAgreement
                <4> QED BY <1>4, <4>1 DEF SetAgreement     
            <3> SUFFICES ASSUME NEW q \in Server,  q#p
                         PROVE set_agreement(p,q)'
                BY <1>t, <3>3 DEF SetAgreement    
            <3>4. flag'.done[p] = 0 BY <1>4, <3>1 DEF ReceiveMessage    
            <3> QED BY <3>4      
        <2>2. CASE recvMsg'.type = "FAIL"
            BY <1>4, <2>2 DEF SetAgreement, ReceiveMessage
        <2>3. CASE (recvMsg'.type # "BCAST" /\ recvMsg'.type # "FAIL")
            BY <1>4, <2>3 DEF SetAgreement, ReceiveMessage    
        <2> QED BY <2>1, <2>2, <2>3
    (* Prove that SetAgreement is preserved by Adeliver(p) *)
    <1>5. ASSUME SetAgreement, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE SetAgreement'
        <2>1. UNCHANGED <<M, flag.nonFaulty>> BY <1>5 DEF Adeliver
        <2>2. \A q \in Server : q # p => UNCHANGED <<flag.done[q]>>
            BY <1>5 DEF Adeliver, TypeInvariant
        <2>3. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2)'
            <3>1. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2) = set_agreement(p1,p2)'
                BY <1>5, <2>1, <2>2 DEF SetAgreement
            <3> QED BY <1>5, <3>1 DEF SetAgreement 
        <2> SUFFICES ASSUME NEW q \in Server,  
                            q # p
                      PROVE set_agreement(p,q)'
            BY <1>t, <2>3 DEF SetAgreement       
        <2> SUFFICES ASSUME flag.nonFaulty[q] = 1, \* q is non-faulty
                            flag.done[q] = 1 \* q terminated
                     PROVE M[p] = M[q]
            BY <1>5, <2>1, <2>2 DEF SetAgreement    
        <2> SUFFICES ASSUME NEW m \in Server,
                            \/ (m \in M[q] /\ m \notin M[p])
                            \/ (m \in M[p] /\ m \notin M[q])
                     PROVE FALSE
            BY DEF TypeInvariant
        <2> DEFINE Mi == IF m \in M[p] THEN M[p] ELSE M[q]
        <2> DEFINE pi == IF m \in M[p] THEN p ELSE q
        <2> DEFINE Mj == IF m \in M[p] THEN M[q] ELSE M[p]
        <2> DEFINE pj == IF m \in M[p] THEN q ELSE p
        (* Prove that the assumption that m is not in Mj implies false *)  
        <2> SUFFICES ASSUME m \in Mi,
                            m \notin Mj
                     PROVE FALSE
            OBVIOUS
        (* m \in Mi => there must be a path P from m's owner to pi, 
                       s.t. every server on P (except m's owner) 
                       has received m from its predecessor *)
        <2>4. PICK P \in PathsFromTo(G,m,pi) : 
                        /\ \A k \in 1..Len(P) : m \in M[P[k]]
                        /\ \A srv \in Server : ((\E k \in 1..Len(P)-1 : P[k+1] \in F[srv][P[k]]) => m \in M[srv])
            BY MessagePath
        (* there must be a server ak on P that did not failed from pj's p.o.w.; 
           pick smallest k with such a property *)
        <2>5. PICK k \in 1..Len(P) : F[pj][P[k]] = {} /\ \A l \in 1..(k-1) : F[pj][P[l]] # {}
            <3> DEFINE Prop(k) == F[pj][P[k+1]] = {}
            <3>1. \E k \in 0..Len(P)-1 : Prop(k)
                <4>1. \A u \in Server : FD[u][P[Len(P)]] = 0 
                    BY <1>5 DEF FDAccuracy, Adeliver, PathsFromTo
                <4>2. Prop(Len(P)-1)  
                    <5>1. \A u \in Server : u \notin F[pj][P[Len(P)]] 
                        BY <4>1, FDGenFail DEF PathsFromTo
                    <5> QED BY <5>1, FDGenFail DEF PathsFromTo, TypeInvariant 
                <4>3. Len(P)-1 \in 0..Len(P)-1 BY DEF PathsFromTo, Path  
                <4> QED BY ONLY <4>2, <4>3    
            <3> HIDE DEF Prop
            <3>2. PICK k_minus \in Nat : Prop(k_minus) /\ \A l \in 0..k_minus-1 : ~Prop(l)
                <4>1. \E k \in Nat : Prop(k) BY <3>1    
                <4> QED BY ONLY <4>1, SmallestNatural
            <3> DEFINE k == k_minus + 1    
            <3>3. k \in  1..Len(P) BY <3>1, <3>2
            <3>4. F[pj][P[k]] = {} BY <3>2 DEF Prop
            <3>5.\A l \in 1..k-1 : F[pj][P[l]] # {} BY <3>2 DEF Prop   
            <3> QED BY <3>3, <3>4, <3>5
        <2>6. P[k] \in Server BY DEF PathsFromTo, Path, G   
        (* The tracking digraph used by pj to track m is empty... *)            
        <2>7. P[k] \notin g[pj][m].node
            <3>1. flag'.done[pj] = 1 BY <1>5 DEF Adeliver, TypeInvariant 
            <3> QED BY <3>1, TerminateTDEmpty    
        (* ... so let's reconstruct the tracking digraph used by pj to track m *)
        <2> DEFINE tgr == ReconstructedTD(pj, m)
        <2>8. \A l \in 1..k :  P[l] \in tgr.node
            (* Let's prove this through natural induction induction *)    
            <3> DEFINE Prop(i) == IF i \leq k-1 THEN P[i+1] \in tgr.node ELSE TRUE
            <3> HIDE DEF Prop
            <3>1. Prop(0) BY <2>4, <2>5, RTDConstruction DEF PathsFromTo, RTDHasRoot, Prop
            <3>2. ASSUME NEW i \in Nat,
                         Prop(i)
                  PROVE Prop(i+1)
                <4>1. CASE i >= k-1 BY <4>1 DEF Prop  
                <4>2. CASE i < k-1 
                    <5>1. P[i+1] \in tgr.node BY ONLY <3>2, <4>2 DEF Prop
                    <5>2. F[pj][P[i+1]] # {}
                        <6>1. \A l \in 1..k-1 : F[pj][P[l]] # {} BY <2>5
                        <6>2. i+1 \in 1..k-1 BY <4>2
                        <6> QED BY <6>1, <6>2
                    <5>3. P[i+2] \in Successors(G,P[i+1])    
                        <6>1. \A l \in 2..k : P[l] \in Successors(G,P[l-1])
                            BY <2>5 DEF PathsFromTo, Path, Successors
                        <6>2. i+2 \in 2..k BY <4>2
                        <6> QED BY <6>1, <6>2
                    <5> QED BY <5>1, <5>2, <5>3, RTDConstruction DEF Prop, RTDFaultyNodeInvariant
                <4> QED BY <4>1, <4>2
            <3>3. \A l \in Nat : Prop(l) BY ONLY <3>1, <3>2, NatInduction
            <3>4. \A l \in 1..k : Prop(l-1) BY <3>3
            <3> QED BY ONLY <3>4 DEF Prop
        <2>9. P[k] \in tgr.node BY ONLY <2>8         
        <2>10. m \notin M[pj] OBVIOUS
        <2>11. F[pj][P[k]] = {} BY <2>5  
        <2>12. PathsFromTo(tgr, m, P[k]) # {}
            <3>1. \A l \in 1..(k-1) : <<P[l], P[l+1]>> \in tgr.edge
                <4> DEFINE all_rtg_edges == {e \in tgr.node \X tgr.node : F[pj][e[1]] # {} /\ e \in G.edge}
                <4> DEFINE rtg_edges == all_rtg_edges \ {e \in all_rtg_edges : e[2] \in F[pj][e[1]] /\ m \notin M[pj]}    
                <4>1. tgr.edge = rtg_edges BY DEF ReconstructedTD
                <4>2. \A l \in 1..(k-1) : <<P[l], P[l+1]>> \in tgr.node \X tgr.node
                    BY <2>8
                <4>3. \A l \in 1..(k-1) : F[pj][P[l]] # {} BY <2>5
                <4>4. \A l \in 1..(k-1) : <<P[l], P[l+1]>> \in G.edge
                    BY <2>4 DEF PathsFromTo, Path
                <4>5. \A l \in 1..(k-1) : P[l+1] \in F[pj][P[l]] => m \in M[pj]
                    BY ONLY <2>4
                <4> QED BY <4>1, <4>2, <4>3, <4>4, <4>5
            <3> DEFINE tgr_path == [l \in 1..k |-> P[l]]
            <3>2. tgr_path \in Seq(tgr.node) BY <2>8
            <3>3. tgr_path # << >>
                <4>1.  Len(tgr_path) # 0 OBVIOUS
                <4> QED BY ONLY <4>1, <3>2, EmptySeq
            <3>4. tgr_path \in  PathsFromTo(tgr, m, P[k]) 
                BY <3>1, <3>2, <3>3, <2>4, <2>8 DEF Path,  PathsFromTo  
            <3> QED BY ONLY <3>4     
        <2> QED BY <2>6, <2>7, <2>9, <2>10, <2>11, <2>12, RTDInvariant DEF RTDInvariant
    (* Prove that SetAgreement is preserved by Fail(p) *)
    <1>6. ASSUME SetAgreement, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE SetAgreement'
        <2>1. UNCHANGED <<M, flag.done>> BY <1>6 DEF Fail
        <2>2. \A q \in Server : q # p => UNCHANGED <<flag.nonFaulty[q]>>
            BY <1>6 DEF Fail, TypeInvariant
        <2>3. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2)'
            <3>1. \A p1, p2 \in Server: (p1#p /\ p2#p) => set_agreement(p1,p2) = set_agreement(p1,p2)'
                BY <1>6, <2>1, <2>2 DEF SetAgreement
            <3> QED BY <1>6, <3>1 DEF SetAgreement     
        <2> SUFFICES ASSUME NEW q \in Server,  q#p
                      PROVE set_agreement(p,q)'
            BY <1>t, <2>3 DEF SetAgreement
        <2>4. flag'.nonFaulty[p] = 0 BY <1>6 DEF Fail, TypeInvariant
        <2> QED BY <2>4  
    (* Prove that SetAgreement is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME SetAgreement, 
                 NEW pj \in Server, 
                 NEW pk \in Server,
                 DetectFailure(pj,pk) 
          PROVE SetAgreement'
        BY <1>7 DEF SetAgreement, DetectFailure 
    <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
    
(* Prove that the set agreement invariant is preserved by the specification Spec *) 
THEOREM SetAgreementInv == Spec => []SetAgreement
    (* Prove stuttering step *) 
    <1>1. SetAgreement /\ UNCHANGED vars => SetAgreement' 
        BY DEF SetAgreement, vars
    (* Prove TypeInvariant *) 
    <1>. Spec => TypeInvariant BY PTL, TypeInv
    (* Prove FDAccuracy *) 
    <1>. Spec => FDAccuracy BY PTL, FDAccuracyInv
    (* Prove RTDInvariant *) 
    <1>. Spec => RTDInvariant BY PTL, RTDInv
    (* Use InitSetAgreementInv and NextSetAgreementInv *)
    <1>2. /\ Spec 
          /\ TypeInvariant 
          /\ FDAccuracy 
          => []SetAgreement
        <2> SUFFICES ASSUME Spec, 
                            TypeInvariant, 
                            FDAccuracy,
                            RTDInvariant 
                     PROVE []SetAgreement
            OBVIOUS
        <2> QED BY PTL, InitSetAgreementInv, NextSetAgreementInv, <1>1 DEF Spec        
    <1> QED BY <1>2 
-----------------------------------------------------------------------------

(* Safety *)
THEOREM AllConcurSafety == Spec => [](Integrity /\ SetAgreement)
    BY IntegrityInv, SetAgreementInv 
    
-----------------------------------------------------------------------------

(***************************************************************************
 * Liveness Properties
 * Validity & Agreement
 ***************************************************************************)
        
(* Liveness *)        
THEOREM AllConcurLiveness == LiveSpec => (Validity /\ Agreement)

=============================================================================