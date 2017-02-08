(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE Naturals_proofs ----------------------
(***************************************************************************)
(* Facts about naturals                                                    *)
(* Source: Rodeheffer TL. The Naiad clock protocol: Specification, model   *) 
(* checking, and correctness proof. Tech. Rep. MSR-TR-2013-20, Microsoft   *)
(* Research, Redmond (Feb 2013)                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, NaturalsInduction, TLAPS

-----------------------------------------------------------------------------

(* Dot dot facts. *)
THEOREM DotDotDef == \A i, m, n \in Nat : (m \leq i /\ i \leq n) <=> i \in m..n 
    BY SMTT(10)
THEOREM DotDotType == \A m, n \in Nat : m..n \subseteq Nat 
    BY SMTT(10)
THEOREM DotDotType2 == \A m, n \in Nat : \A i \in m..n : i \in Nat 
    BY SMTT(10)
        
(* 1..n is equivalent to n itself for n \in Nat. *)
THEOREM DotDotOneThruN == \A m, n \in Nat : 1..m = 1..n <=> m = n
    <1>1. SUFFICES ASSUME NEW m \in Nat, NEW n \in Nat, m # n 
                   PROVE 1..m # 1..n 
          OBVIOUS
    (* Without loss of generality, assume ma is smaller than na. *)
    <1> DEFINE ma == IF m < n THEN m ELSE n
    <1> DEFINE na == IF m < n THEN n ELSE m
    <1>2. ma \in Nat OBVIOUS
    <1>3. na \in Nat OBVIOUS
    <1>4. ma < na
        <2>1. CASE m < n 
            BY <2>1, <1>1, SMTT(10)
        <2>2. CASE ~(m < n) 
            BY <2>2, <1>1, SMTT(10)
        <2> QED BY <2>1, <2>2
    <1> SUFFICES 1..ma # 1..na 
        BY SMTT(10)
    <1> HIDE DEF ma, na
    (* na shows that the ranges differ. *)
    <1>5. 0 < na BY <1>2, <1>3, <1>4, SMTT(10)
    <1>6. 1 \leq na BY <1>3, <1>5, SMTT(10)
    <1>7. na \in 1..na BY <1>3, <1>6, SMTT(10)
    <1>8. na \notin 1..ma BY <1>2, <1>3, <1>4, SMTT(10)
    <1> QED BY <1>7, <1>8
    
(* Any non-empty subset of Nat has a minimum element. You would think this 
   would be a library theorem, but I could not find it. We use the classic
   inductive proof by contradiction for this theorem. *)
THEOREM NatWellFounded == \A N \in SUBSET Nat : N # {} => \E n \in N : \A m \in N : n \leq m
    <1>1. SUFFICES ASSUME NEW N \in SUBSET Nat, N # {}
                   PROVE \E n \in N : \A m \in N : n \leq m
          OBVIOUS        
    (* Assuming that no minimum element of N exists, we prove that N must be empty, 
       which is a contradiction. *)
    <1>2. SUFFICES ASSUME ~\E n \in N : \A m \in N : n \leq m 
                   PROVE N = {} 
           BY <1>1
    (* P(i) says that no naturals less than i are in N. We prove this for all i 
       in Nat using induction. *)
    <1> DEFINE P(i) == \A k \in Nat : k < i => k \notin N
    <1>3. \A i \in Nat : P(i)
        <2>1. P(0) BY SMTT (10)
        <2>2. \A i \in Nat : P (i) => P(i + 1)
            <3>1. SUFFICES ASSUME NEW i \in Nat, P(i) 
                           PROVE P(i + 1) 
                  OBVIOUS
            <3>2. SUFFICES ASSUME NEW k \in Nat, k < i + 1 
                           PROVE k \notin N 
                  OBVIOUS
            <3>3. CASE k < i 
                BY <3>1, <3>3
            <3>4. CASE k = i
                <4>1. SUFFICES ASSUME k \in N 
                               PROVE FALSE 
                      OBVIOUS
                <4>2. \A j \in N : k \leq j BY <3>1, <3>4, SMTT(10)
                <4> QED BY <4>1, <4>2, <1>2
            <3> QED BY <3>2, <3>3, <3>4, SMTT(10)
        <2> HIDE DEF P
        <2> QED BY ONLY <2>1, <2>2, NatInduction, Isa
    (* Since P(i) is true for all i in Nat, N must be empty. *)
    <1>4. \A i \in Nat : i \notin N
        <2> SUFFICES ASSUME NEW i \in Nat 
                     PROVE i \notin N 
            OBVIOUS
        <2>1. i + 1 \in Nat BY SMTT(10)
        <2>2. P(i + 1) BY <2>1, <1>3
        <2>3. i < i + 1 BY SMTT(10)
        <2> QED BY <2>2, <2>3
    <1> QED BY <1>4
=============================================================================