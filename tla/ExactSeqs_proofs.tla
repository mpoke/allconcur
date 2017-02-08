(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE ExactSeqs_proofs ---------------------
(***************************************************************************)
(* Facts about sequences                                                   *)
(* Source: Rodeheffer TL. The Naiad clock protocol: Specification, model   *) 
(* checking, and correctness proof. Tech. Rep. MSR-TR-2013-20, Microsoft   *)
(* Research, Redmond (Feb 2013)                                            *)
(***************************************************************************)
EXTENDS ExactSeqs, Naturals_proofs, NaturalsInduction, SequenceTheorems, TLAPS

-----------------------------------------------------------------------------

THEOREM CorrectIsFiniteSet == 
    \A S : IsFiniteSet(S) <=> \E seq \in Seq(S) : \A s \in S : \E n \in 1..Len(seq) : seq[n] = s
    OMITTED

(* Prove that q \in Seq(S).
   For some reason, the provers find it difficult to deduce this from the 
   given predicates using just SeqDef, so it helps to prove it once here. *)
THEOREM LocalIsASeq == 
    ASSUME NEW S, NEW n \in Nat, NEW q \in [1..n -> S]
    PROVE q \in Seq(S)
    <1> QED BY SeqDef, IsaT(120)

(* An exact sequence exists for any finite set. *)
THEOREM ExactSeqExists ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE \E Q : IsExactSeqFor(Q, S)
    <1> USE DEF ExactSeq_Each
    <1> USE DEF ExactSeq_Once
    <1> DEFINE each(Q) == ExactSeq_Each(Q, S)
    <1> DEFINE once(Q) == ExactSeq_Once(Q)
    <1> SUFFICES \E n \in Nat : \E Q \in [1..n -> S] : each(Q) /\ once(Q)
        <2>1. PICK n \in Nat : \E Q \in [1..n -> S] : each(Q) /\ once(Q)
            OBVIOUS
        <2>2. PICK Q \in [1..n -> S] : each(Q) /\ once(Q)
            BY <2>1
        <2>3. Q \in Seq(S) BY LocalIsASeq
        <2> QED BY <2>2, <2>3 DEF IsExactSeqFor
   (* Define N as the set of all natural numbers n such that there exists 
      a sequence of length n that contains each element of S. Because S is finite,
      such a sequence exists and hence N is non-empty. *)
    <1> DEFINE N == {n \in Nat : \E Q \in [1..n -> S] : each(Q)}
    <1>1. N # {}
        <2>1. PICK Q \in Seq(S) : each(Q) 
            BY CorrectIsFiniteSet
        <2>2. Len(Q) \in Nat BY LenProperties
        <2>3. Q \in [1..Len(Q) -> S] BY <2>1, LenProperties
        <2>4. Len(Q) \in N BY <2>1, <2>2, <2>3
        <2> QED BY <2>4
    <1> HIDE DEF N 
    (* Pick the smallest n \in N *)
    <1>2. PICK n \in Nat :
            /\ n \in N
            /\ \A m \in N : n \leq m
        <2>1. PICK n \in N : \A m \in N : n \leq m
            <3>1. N \in SUBSET Nat BY DEF N
            <3> QED BY <3>1, <1>1, NatWellFounded
        <2>2. n \in Nat BY DEF N
        <2> QED BY <2>1, <2>2
    (* Pick Q a sequence of length n that contains each element of S. 
       Since this is the smallest such length, Q can contain no duplicates. *)
    <1>3. PICK Q \in [1..n -> S] : each(Q)
        <2>1. n \in N 
            BY <1>2
        <2> QED BY <2>1 DEF N
    <1>4. SUFFICES once(Q)
        <2> HIDE DEF each, once
        <2> QED BY <1>2, <1>3, <1>4 DEF N
    (* To show that every element on Q appears at most once, we assume that 
       Q contains duplicates and derive a contradiction. *)
    <1>5. SUFFICES ASSUME ~once(Q) 
                   PROVE FALSE 
          OBVIOUS
    (* It turns out to be important to know that Len(Q) = n and is a natural. *)
    <1> DEFINE LenQ == Len(Q)
    <1> HIDE DEF LenQ
    <1>6. LenQ = n /\ LenQ \in Nat
        <2>1. Q \in Seq(S) BY LocalIsASeq
        <2>2. LenQ \in Nat BY <2>1, LenProperties DEF LenQ
        <2>3. DOMAIN Q = 1..LenQ BY <2>1, LenProperties DEF LenQ
        <2>4. 1..LenQ = 1..n BY <2>3
        <2>5. LenQ = n BY <2>2, <2>4, DotDotOneThruN
        <2> QED BY <2>5
    (* Under the assumption that Q has duplicate elements, we can pick two distinct 
       indexes j and k containing the same element. Without loss of generality, 
       let j be the smaller index. *)
    <1>7. PICK j, k \in Nat : Q[j] = Q[k] /\ 1 \leq j /\ j < k /\ k \leq LenQ
        <2> LenQ \in Nat 
            BY <1>6
        <2>1. PICK ja, ka \in 1..LenQ : Q[ja] = Q[ka] /\ ja # ka 
            BY <1>5 DEF LenQ
        <2> ja \in Nat BY <2>1, SMTT(10)
        <2> ka \in Nat BY <2>1, SMTT(10)
        <2>2. 1 \leq ja BY <2>1, SMTT(10)
        <2>3. 1 \leq ka BY <2>1, SMTT(10)
        <2>4. ja \leq LenQ BY <2>1, SMTT(10)
        <2>5. ka \leq LenQ BY <2>1, SMTT(10)
        <2>6. CASE ja < ka 
            BY <2>6, <2>1, <2>2, <2>5
        <2>7. CASE ka < ja 
            BY <2>7, <2>1, <2>3, <2>4
        <2>8. ja < ka \/ ka < ja
            <3>1. LenQ \in Nat BY <1>6
            <3>2. ja \in Nat BY <3>1, DotDotType
            <3>3. ka \in Nat BY <3>1, DotDotType
            <3> QED BY <2>1, <3>2, <3>3, SMTT(10)
        <2> QED BY <2>1, <2>6, <2>7, <2>8, <1>6, SMTT(10)
    (* Define m = n − 1 and prove some properties of j, k, m, n. 
       Later we construct a sequence P of length m. *)
    <1>8. 1 \leq j BY <1>7, SMTT(10)
    <1>9. j < k BY <1>7
    <1>10. k \leq n BY <1>6, <1>7, SMTT(10)
    <1>11. 1 < k BY <1>8, <1>9, SMTT(10)
    <1>12. 1 \leq k BY <1>11, SMTT(10)
    <1>13. 2 \leq n BY <1>10, <1>11, SMTT(10)
    <1>14. n # 0 BY <1>13, SMTT(10)
    <1>15. n - 1 \in Nat BY <1>14, SMTT(10)
    <1>16. PICK m \in Nat : m = n - 1 
        BY <1>15
    <1>17. m < n BY <1>16, SMTT(10)
    <1>18. ~(n \leq m) BY <1>17, SMTT(10)
    <1>19. j < n BY <1>9, <1>10, SMTT(10)
    <1>20. j \leq m BY <1>16, <1>19, SMTT(10)
    <1>21. j \in 1..m BY <1>8, <1>20, SMTT(10)
    <1>22. n \in 1..n BY <1>14, SMTT(10)
    <1>23. ASSUME k # n 
           PROVE k \in 1..m
        <2>1. k \leq m BY <1>10, <1>16, <1>23, SMTT(10)
        <2> QED BY <1>12, <2>1, SMTT(10)
    <1>24. ASSUME NEW i \in 1..n, i # n 
                  PROVE i \in 1..m
        <2>1. 1 \leq i BY <1>24, SMTT(10)
        <2>2. i \leq n BY <1>24, SMTT(10)
        <2>3. i < n BY <1>24, <2>2, SMTT(10)
        <2>4. i \leq m BY <2>3, <1>16, SMTT(10)
        <2> QED BY <2>1, <2>4, SMTT(10)
    (* Construct P from Q as a shorter sequence in which each element of S appears. 
       However, since Q is the shortest such sequence, this is a contradiction. *)
    <1> DEFINE P == [i \in 1..m |-> IF i = k THEN Q[n] ELSE Q[i]]
    <1>25. P \in [1..m -> S]
        <2> SUFFICES ASSUME NEW i \in 1..m 
                     PROVE P[i] \in S 
            BY SMTT(10)
        <2>1. i \in 1..n BY <1>16, SMTT(10)
        <2>2. n \in 1..n BY <1>22
        <2>3. Q[i] \in S BY <2>1
        <2>4. Q[n] \in S BY <2>2
        <2> QED BY <2>3, <2>4
    <1> HIDE DEF P
    <1>26. SUFFICES each(P)
        <2>2. m \in N BY <1>25, <1>26 DEF N
        <2> HIDE DEF each
        <2>3. ~(n \leq m) BY <1>18
        <2> QED BY <2>2, <2>3, <1>2, SMTT(10)                
    (* To show that each element of S appears in P, we assume that P has missing 
       elements and derive a contradiction. *)
    <1>27. SUFFICES ASSUME ~each(P) 
                    PROVE FALSE 
           OBVIOUS
    (* It turns out to be important to know that Len(P ) = m and is a natural. *)
    <1> DEFINE LenP == Len(P)
    <1> HIDE DEF LenP
    <1>28. LenP = m /\ LenP \in Nat
        <2> HIDE DEF P
        <2>2. P \in Seq(S) BY <1>25, LocalIsASeq
        <2>3. LenP \in Nat BY <2>2, LenProperties DEF LenP
        <2>4. DOMAIN P = 1..LenP BY <2>2, LenProperties DEF LenP
        <2>5. 1..LenP = 1..m BY <2>4, <1>25
        <2>6. LenP = m BY <2>3, <2>5, DotDotOneThruN
        <2> QED BY <2>6
    (* Since we assume that P has missing elements, we can pick an element that 
       fails to appear. But this element appears on Q, from which we can find it on P, 
       thus establishing a contradiction. *)
    <1>29. PICK s \in S : ~\E i \in 1..LenP : P [i] = s 
        BY <1>27 DEF LenP
    <1>30. PICK i \in 1..n : Q[i] = s 
        BY <1>3, <1>6 DEF LenQ
    <1>31. CASE i = k
    (* A duplicate of Q[k] appears in Q[j]. Since j = k and j \in 1..m, we copied 
       Q[j] to P[j]. *)
        <2>1. j # k BY <1>9, SMTT(10)
        <2>2. P[j] = Q[j] BY <2>1, <1>21 DEF P
        <2>3. Q[j] = Q[k] BY <1>7
        <2>4. P[j] = s BY <2>2, <2>3, <1>31, <1>30
        <2>5. j \in 1..LenP BY <1>21, <1>28
        <2> QED BY <2>4, <2>5, <1>29
    <1>32. CASE i # k /\ i = n
    (* Since k \in 1..m, we copied Q[n] to P[k]. *)
        <2>1. k \in 1..m BY <1>32, <1>23
        <2>2. P[k] = Q[n] BY <2>1 DEF P
        <2>3. P[k] = s BY <2>2, <1>32, <1>30
        <2>4. k \in 1..LenP BY <2>1, <1>28, SMTT(10)
        <2> QED BY <2>3, <2>4, <1>29
    <1>33. CASE i # k /\ i # n
    (* Since i # k and i \in 1..m, we copied Q[i] to P[i]. *)
        <2>1. i # k /\ i \in 1..m BY <1>33, <1>24
        <2>2. P[i] = Q[i] BY <2>1 DEF P
        <2>3. P[i] = s BY <2>2, <1>31, <1>30
        <2>4. i \in 1..LenP BY <2>1, <1>28
        <2> QED BY <2>3, <2>4, <1>29
    <1> QED BY <1>31, <1>32, <1>33
    
(* If S is a finite set, then ExactSeqFor (S ) is an exact sequence for S. *)
THEOREM ExactSeqForProperties ==
    ASSUME NEW S, IsFiniteSet(S)
    PROVE IsExactSeqFor(ExactSeqFor(S), S)
    <1> QED 
        BY ExactSeqExists DEF ExactSeqFor    
     
=============================================================================