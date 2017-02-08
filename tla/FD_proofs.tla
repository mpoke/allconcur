(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE FD_proofs ----------------------------
EXTENDS AllConcur, SequenceTheorems, FiniteSetTheorems, TypeInvariant_proofs, TLAPS

-----------------------------------------------------------------------------

(* FDAccuracy

FDAccuracy == \* PROPERTY: FD Accuracy
    \A p \in Server : flag.nonFaulty[p] = 1 => (\A q \in Server : FD[q][p] = 0)
*)   
THEOREM InitFDAccuracyInv == Init => FDAccuracy 
    BY DEF Init, FDAccuracy
    
THEOREM NextFDAccuracyInv == TypeInvariant /\ FDAccuracy /\ Next => FDAccuracy'
    <1> SUFFICES ASSUME /\ TypeInvariant 
                 PROVE FDAccuracy /\ Next => FDAccuracy'
        OBVIOUS
    <1>1. SUFFICES /\ (FDAccuracy /\ \E p \in Server : Abcast(p)) => FDAccuracy'
                   /\ (FDAccuracy /\ \E p \in Server : TXMessage(p)) => FDAccuracy'
                   /\ (FDAccuracy /\ \E p \in Server : ReceiveMessage(p)) => FDAccuracy'
                   /\ (FDAccuracy /\ \E p \in Server : Adeliver(p)) => FDAccuracy'
                   /\ (FDAccuracy /\ \E p \in Server : Fail(p)) => FDAccuracy'
                   /\ (FDAccuracy /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => FDAccuracy'
        BY DEF Next 
    (* Prove that FDAccuracy is preserved by Abcast(p) *)
    <1>2. ASSUME FDAccuracy, 
                 NEW p \in Server, 
                 Abcast(p) 
          PROVE FDAccuracy'
        BY <1>2 DEF Abcast, FDAccuracy
    (* Prove that FDAccuracy is preserved by TXMessage(p) *)      
    <1>3. ASSUME FDAccuracy, 
                 NEW p \in Server, 
                 TXMessage(p) 
          PROVE FDAccuracy'
        BY <1>3 DEF TXMessage, FDAccuracy
    (* Prove that FDAccuracy is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME FDAccuracy, 
                 NEW p \in Server, 
                 ReceiveMessage(p) 
          PROVE FDAccuracy'
        <2>1. UNCHANGED <<FD>> BY ONLY <1>4 DEF ReceiveMessage
        <2>2. UNCHANGED <<flag.nonFaulty>> BY <1>4 DEF ReceiveMessage,  ReceiveBCAST, TypeInvariant 
        <2> QED BY ONLY <1>4, <2>1, <2>2 DEF FDAccuracy
    (* Prove that FDAccuracy is preserved by Adeliver(p) *)
    <1>5. ASSUME FDAccuracy, 
                 NEW p \in Server, 
                 Adeliver(p) 
          PROVE FDAccuracy'
        BY <1>5 DEF Adeliver, FDAccuracy
    (* Prove that FDAccuracy is preserved by Fail(p) *)
    <1>6. ASSUME FDAccuracy, 
                 NEW p \in Server, 
                 Fail(p) 
          PROVE FDAccuracy'
        <2>1. SUFFICES ASSUME NEW pj \in Server, 
                              NEW pk \in Server,
                              flag.nonFaulty[pj] = 1 => FD[pk][pj] = 0
                       PROVE flag'.nonFaulty[pj] = 1 => FD'[pk][pj] = 0
            BY <1>6 DEF FDAccuracy
        <2>2. UNCHANGED <<FD>> BY ONLY <1>6 DEF Fail    
        <2>3. CASE pj = p
            <3>1. flag.nonFaulty[pj] = 1 BY ONLY <2>3, <1>6 DEF Fail
            <3>2. FD[pk][pj] = 0 BY ONLY <3>1, <2>1
            <3> QED BY ONLY <3>2, <2>2 
        <2>4. CASE pj # p
            <3>1. UNCHANGED <<flag.nonFaulty[pj]>> BY <2>4, <1>6 DEF Fail, TypeInvariant
            <3> QED BY ONLY <2>1, <2>2, <3>1
        <2> QED BY ONLY <2>3, <2>4 
    (* Prove that FDAccuracy is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME FDAccuracy, 
                 NEW pf \in Server, 
                 NEW pd \in Server,
                 DetectFailure(pf,pd) 
          PROVE FDAccuracy'
        <2>1. SUFFICES ASSUME NEW pj \in Server, 
                              NEW pk \in Server,
                              flag.nonFaulty[pj] = 1 => FD[pk][pj] = 0
                       PROVE flag'.nonFaulty[pj] = 1 => FD'[pk][pj] = 0
            BY <1>7 DEF FDAccuracy
        <2>2. UNCHANGED <<flag>> BY ONLY <1>7 DEF DetectFailure
        <2>3. CASE pd = pk
            <3>1. CASE pf = pj
                <4>1. flag.nonFaulty[pj] = 0 BY ONLY <1>7, <2>3, <3>1 DEF DetectFailure
                <4> QED BY ONLY <2>1, <2>2, <4>1
            <3>2. CASE pf # pj
                <4>1. UNCHANGED <<FD[pk][pj]>> BY <3>2, <1>7 DEF DetectFailure, TypeInvariant
                <4> QED BY ONLY <2>1, <2>2, <4>1
            <3> QED BY ONLY <3>1, <3>2
        <2>4. CASE pd # pk
            <3>1. UNCHANGED <<FD[pk]>> BY <2>4, <1>7 DEF DetectFailure, TypeInvariant
            <3> QED BY ONLY <2>1, <2>2, <3>1
        <2> QED BY ONLY <2>3, <2>4
    <1> QED BY ONLY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7    

THEOREM FDAccuracyInv == Spec => []FDAccuracy    
    (* Prove stuttering step *) 
    <1>1. FDAccuracy /\ UNCHANGED vars => FDAccuracy' 
        BY DEF FDAccuracy, vars
    (* Prove TypeInvariant *) 
    <1>2. Spec => TypeInvariant BY PTL, TypeInv
    (* Use InitFDAccuracyInv and NextFDAccuracyInv *)
    <1>3. Spec /\ TypeInvariant => []FDAccuracy
        <2> SUFFICES ASSUME Spec, TypeInvariant 
                     PROVE []FDAccuracy
            OBVIOUS
        <2> QED BY PTL, InitFDAccuracyInv, NextFDAccuracyInv, <1>1 DEF Spec    
    <1> QED BY <1>2, <1>3
    
(* Clearly, failure notificaiton are generated by failure detection *)    
THEOREM FDGenFail ==
    \A pi,pj,pk \in Server : FD[pk][pj] = 0 => pk \notin F[pi][pj]
    OMITTED
    
(* FDCompleteness

FDCompleteness == \* PROPERTY: FD Completeness
    \* whenever a server p fails, EVENTUALLY every non-faulty successors of p detects p's failure
    \A p \in Server : flag.nonFaulty[p] = 0 ~> (\A q \in Successors(G, p) : flag.nonFaulty[q] = 1 => FD[q][p] = 1)
*)    

=============================================================================