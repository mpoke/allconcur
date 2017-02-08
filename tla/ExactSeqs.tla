(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE ExactSeqs ----------------------------
(***************************************************************************)
(* Create a sequence out of a set                                          *)
(* Source: Rodeheffer TL. The Naiad clock protocol: Specification, model   *) 
(* checking, and correctness proof. Tech. Rep. MSR-TR-2013-20, Microsoft   *)
(* Research, Redmond (Feb 2013)                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

-----------------------------------------------------------------------------

ExactSeq_Each(Q, S) == \* Each s \in S apprears on Q 
    \A s \in S : \E i \in 1..Len(Q): Q[i] = s

ExactSeq_Once(Q) == \* Anything on Q appears at most once 
    \A i,j \in 1..Len(Q) : Q[i] = Q[j] => i = j

IsExactSeqFor(Q, S) == \* Q is an exact sequence for the set S 
    /\ Q \in Seq(S)
    /\ ExactSeq_Each(Q, S)
    /\ ExactSeq_Once(Q)

ExactSeqFor(S) == \* For any finite set S, choose a sequence in which each element of S appears exactly once.
    \* CHOOSE Q \in [1..Cardinality(S) -> S] : IsExactSeqFor(Q, S)    
    CHOOSE Q  : IsExactSeqFor(Q, S)
    
=============================================================================