(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE TypeInvariant_proofs -----------------
EXTENDS AllConcur, NaturalsInduction, SequenceTheorems, FiniteSetTheorems, 
        ExactSeqs_proofs, TLAPS

-----------------------------------------------------------------------------
(* AXIOMS *)

(* This is obvious, however, not that trivial to prove with TLAPS *)        
AXIOM FiniteServer == IsFiniteSet(Server)

-----------------------------------------------------------------------------
(* Helping theorems *)

(* Trivial theorem that helps with some cases *)
THEOREM FunctionExcept ==
  ASSUME NEW S, NEW T, NEW fun \in [S -> T], NEW s \in S, NEW e \in T 
  PROVE  [fun EXCEPT ![s] = e] \in [S -> T]
    OBVIOUS
    
(* The type of the send buffer remains the same after sending a message *) 
THEOREM SendMessageTypeInv == 
    ASSUME TypeInvariant,
           NEW p \in Server, 
           NEW msgs \in Seq(Message),
           SendMessage(p, msgs, flag.nonFaulty)
    PROVE sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
    <1> USE DEF TypeInvariant, NetTypeInvariant, SendMessage
    <1> DEFINE SendTo(i) == SendMessage(p, msgs, flag.nonFaulty)!1!SendTo(i)  
    <1> DEFINE buf == [i \in 1..Len(msgs) |-> <<msgs[i], ExactSeqFor(SendTo(i))>>]
    <1>1. buf \in Seq(Message \X Seq(Server))
        <2>1. \A i \in 1..Len(msgs) : SendTo(i) \subseteq Server
            BY DEF G, Successors     
        <2> SUFFICES ASSUME NEW i \in 1..Len(msgs) 
                     PROVE <<msgs[i], ExactSeqFor(SendTo(i))>> \in Message \X Seq(Server)
            BY IsASeq
        <2> HIDE DEF SendTo    
        <2> SUFFICES ExactSeqFor(SendTo(i)) \in Seq(Server)
            <3>2. msgs[i] \in Message BY DEF Message
            <3> QED BY <3>2  
        <2>2. IsExactSeqFor(ExactSeqFor(SendTo(i)), SendTo(i))
            <3>1. IsFiniteSet(SendTo(i)) BY <2>1, FS_Subset, FiniteServer
            <3> QED BY <3>1, ExactSeqForProperties
        <2> QED BY <2>1, <2>2 DEF IsExactSeqFor
    <1>2. sendBuf'[p] = sendBuf[p] \o buf
        OBVIOUS
    <1>3. sendBuf'[p] \in Seq(Message \X Seq(Server)) 
        <2>1. sendBuf[p] \in Seq(Message \X Seq(Server)) OBVIOUS
        <2> QED BY <1>1, <1>2, <2>1
    <1>4. sendBuf' = [sendBuf EXCEPT ![p] = sendBuf[p] \o buf] OBVIOUS         
    <1> QED BY <1>3, <1>4,  FunctionExcept 
    
-----------------------------------------------------------------------------
(* TypeInvariant *)
              
(* Prove that the TypeInvariant holds for the initial state *)   
THEOREM InitTypeInv == Init => TypeInvariant
    <1> SUFFICES ASSUME Init
                 PROVE TypeInvariant
        OBVIOUS
    <1> USE DEF Init, TypeInvariant, NetInit, NetTypeInvariant
    (* Handle (CHOOSE m \in Message : TRUE) \in Message *)
    <1> DEFINE P(x) == TRUE
    <1> DEFINE foo == CHOOSE m \in Message : P(m)
    <1> DEFINE Q(x) == x \in Message
    <1> SUFFICES Q(foo) BY DEF DigraphType
    <1>1. CASE \E m \in Message : P(m)
        <2>1. \A m \in Message : P(m) => Q(m) OBVIOUS
        <2> QED BY <1>1, <2>1 DEF Q 
    <1>2. CASE ~ \E m \in Message : P(m)
        <2> SUFFICES ASSUME ~ \E m \in Message : P(m)
                     PROVE FALSE
            OBVIOUS
        <2> DEFINE msg == [type |-> "BCAST", owner |-> 0]
        <2>1. msg \in Message 
            <3>1. 0 \in Server BY ServerCountNat, DotDotDef DEF Server
            <3> QED BY <3>1 DEF Message
        <2>2. P(msg) OBVIOUS    
        <2> QED BY <2>1, <2>2    
    <1> QED BY <1>1, <1>2
            
(* Prove that the TypeInvariant is preserved by the next-state relation Next *)         
THEOREM NextTypeInv == TypeInvariant /\ Next => TypeInvariant'
    <1>1. SUFFICES /\ (TypeInvariant /\ \E p \in Server : Abcast(p)) => TypeInvariant'
                   /\ (TypeInvariant /\ \E p \in Server : TXMessage(p)) => TypeInvariant'
                   /\ (TypeInvariant /\ \E p \in Server : ReceiveMessage(p)) => TypeInvariant'
                   /\ (TypeInvariant /\ \E p \in Server : Adeliver(p)) => TypeInvariant'
                   /\ (TypeInvariant /\ \E p \in Server : Fail(p)) => TypeInvariant'
                   /\ (TypeInvariant /\ \E p \in Server : (\E q \in Server : DetectFailure(p,q))) => TypeInvariant'
        BY DEF Next
    (* Prove that the TypeInvariant is preserved by Abcast(p) *) 
    <1>2. ASSUME TypeInvariant, NEW p \in Server, Abcast(p) 
          PROVE TypeInvariant'
        <2> USE TypeInvariant, Abcast(p) DEF TypeInvariant, NetTypeInvariant, Abcast
        <2>1. M'[p] \in SUBSET Server OBVIOUS
        <2>2. flag'.abcast[p] \in {0,1} OBVIOUS     
        <2>3. g'[p][p] \in DigraphType(Server) BY DEF DigraphType
        <2>4. sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
            <3> DEFINE msgs == <<[type |-> "BCAST", owner |-> p]>>
            <3>1. msgs \in Seq(Message) BY DEF Message
            <3> QED BY SendMessageTypeInv, <3>1 
        <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF SendMessage   
    (* Prove that the TypeInvariant is preserved by TXMessage(p) *)
    <1>3. ASSUME TypeInvariant, NEW p \in Server, TXMessage(p) 
          PROVE TypeInvariant'
          <2> USE TypeInvariant, TXMessage(p) DEF TypeInvariant, NetTypeInvariant, TXMessage, NetTXMessage
          <2> DEFINE msg == Head(sendBuf[p])[1]
          <2> DEFINE succ == Head(sendBuf[p])[2]
          <2> SUFFICES /\ sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
                       /\ recvBuf' \in [Server -> Seq(Message)]
            OBVIOUS  
          <2>1. CASE succ = << >>
             <3>1. recvBuf' = recvBuf BY <2>1
             <3>2. sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
                <4>1. sendBuf'[p] = Tail(sendBuf[p]) BY <2>1
                <4> QED BY <2>1, <4>1, FunctionExcept
             <3> QED BY <3>1, <3>2
          <2>2. CASE succ # << >>
             <3> DEFINE next == Head(succ)
             <3>1. recvBuf'[next] = Append(recvBuf[next], msg) BY <2>2
             <3> HIDE DEF next
             <3>2. sendBuf'[p] \in Seq(Message \X Seq(Server))
                <4> DEFINE sendBuf_p_head == [sendBuf[p][1] EXCEPT ![2] = Tail(succ)]
                <4>1. sendBuf_p_head \in Message \X Seq(Server)
                    <5>1. Tail(succ) \in Seq(Server) BY <2>2
                    <5>2. sendBuf[p][1] \in Message \X Seq(Server)
                        <6>1. sendBuf[p][1] = Head(sendBuf[p]) OBVIOUS
                        <6>2. Head(sendBuf[p]) \in Message \X Seq(Server) BY HeadTailProperties
                        <6> QED BY <6>1, <6>2
                    <5> QED BY <5>1, <5>2
                <4> HIDE DEF sendBuf_p_head
                <4> DEFINE sendBuf_p == [sendBuf[p] EXCEPT ![1] = sendBuf_p_head]
                <4>2. sendBuf_p \in Seq(Message \X Seq(Server)) BY <4>1
                <4> HIDE DEF sendBuf_p
                <4>3. sendBuf'[p] = sendBuf_p BY <2>2 DEF sendBuf_p, sendBuf_p_head
                <4> QED BY <4>2, <4>3
             <3> QED BY <3>1, <3>2
          <2> QED BY <2>1, <2>2
    (* Prove that the TypeInvariant is preserved by ReceiveMessage(p) *)
    <1>4. ASSUME TypeInvariant, NEW p \in Server, ReceiveMessage(p) 
          PROVE TypeInvariant'
          <2> USE TypeInvariant,  ReceiveMessage(p) DEF TypeInvariant, NetTypeInvariant, ReceiveMessage
          <2>1. recvMsg' \in Message BY DEF DeliverMessage
          <2>2. recvBuf'[p] \in Seq(Message) BY DEF DeliverMessage
          <2> DEFINE m == recvMsg'
          <2>3. CASE recvMsg'.type = "BCAST"
            <3> USE <2>3
            <3> m.owner \in Server BY <2>1 DEF Message
            <3>1. CASE flag.abcast[m.owner] = 1 /\ m.owner \notin M[p]
                <4> USE <3>1  
                <4>1. CASE flag.abcast[p] = 0
                    <5> USE <4>1
                    <5>1. sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
                        <6>1. <<[type |-> "BCAST", owner |-> p], m>> \in Seq(Message) 
                            BY <2>1 DEF Message
                        <6> QED BY <6>1, SendMessageTypeInv DEF ReceiveBCAST
                    <5>2. M'[p] \in SUBSET Server 
                        <6>1. {p,m.owner} \in SUBSET Server OBVIOUS
                        <6>2. M'[p] = M[p] \cup {p,m.owner} BY DEF ReceiveBCAST
                        <6> QED BY <6>1, <6>2
                    <5>3. g'[p] \in [Server -> DigraphType(Server)]
                        <6> DEFINE g1 == [g EXCEPT ![p] =  [g[p] EXCEPT ![p] = [node |-> {}, edge |-> {}]]]
                        <6>1. g1 \in [Server -> [Server -> DigraphType(Server)]]
                            BY DEF ReceiveBCAST, DigraphType
                        <6> HIDE DEF g1
                        <6> DEFINE g2_p == [g EXCEPT ![p] = [g[p] EXCEPT ![p] = [node |-> {}, edge |-> {}]]][p]
                        <6>2. g2_p \in [Server -> DigraphType(Server)]
                            BY DEF ReceiveBCAST, DigraphType
                        <6> HIDE DEF g2_p
                        <6> DEFINE g2 == [g1 EXCEPT ![p] = [g2_p EXCEPT ![(recvMsg').owner] = [node |-> {},edge |-> {}]]]
                        <6>3. g2 \in [Server -> [Server -> DigraphType(Server)]]
                            BY <6>1, <6>2 DEF ReceiveBCAST, DigraphType
                        <6> HIDE DEF g2
                        <6>4. g' = g2 BY DEF ReceiveBCAST, g2, g2_p, g1
                        <6> QED BY <6>3, <6>4
                    <5>4. flag'.abcast \in [Server -> {0, 1}] 
                        <6>1. flag.abcast \in [Server -> {0, 1}] OBVIOUS
                        <6>2. flag'.abcast = [flag.abcast EXCEPT ![p] = 1]  
                            BY DEF ReceiveBCAST
                        <6> QED BY <6>1, <6>2, FunctionExcept                           
                    <5> QED BY <2>1, <2>2, <5>1, <5>2, <5>3, <5>4 
                            DEF DeliverMessage, ReceiveBCAST, SendMessage
                <4>2. CASE flag.abcast[p] # 0
                    <5> USE <4>2
                    <5>1. sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
                        <6>1. <<m>> \in Seq(Message) BY <2>1 DEF Message
                        <6> QED BY <6>1, SendMessageTypeInv DEF ReceiveBCAST
                    <5>2. M'[p] \in SUBSET Server 
                        BY DEF ReceiveBCAST
                    <5>3. g'[p] \in [Server -> DigraphType(Server)]
                        <6>1. g'[p][m.owner] \in DigraphType(Server)
                            BY DEF ReceiveBCAST, DigraphType   
                        <6> QED BY <6>1 DEF ReceiveBCAST, DigraphType
                    <5> QED BY <2>1, <2>2, <5>1, <5>2, <5>3 
                            DEF DeliverMessage, ReceiveBCAST, SendMessage
                <4> QED BY <4>1, <4>2
            <3>2. CASE ~ (flag.abcast[m.owner] = 1 /\ m.owner \notin M[p])
                BY <2>1, <2>2, <3>2 DEF DeliverMessage, ReceiveBCAST
            <3> QED BY <3>1, <3>2
          <2>4. CASE recvMsg'.type = "FAIL"
            <3> USE <2>4
            <3> m.owner \in Server BY <2>1 DEF Message
            <3> m.target \in Server BY <2>1 DEF Message
            <3>1. CASE m.owner \notin F[p][m.target]
                <4> USE <3>1
                <4>1. sendBuf' \in [Server -> Seq(Message \X Seq(Server))]
                    <5>1. <<m>> \in Seq(Message) BY <2>1 DEF Message
                    <5> QED BY <5>1, SendMessageTypeInv DEF ReceiveFAIL
                <4>2. F' \in [Server -> [Server -> SUBSET Server]]
                    <5> DEFINE F_p == [F[p] EXCEPT ![m.target] = F[p][m.target] \cup  {m.owner}]
                    <5>1. F_p \in [Server -> SUBSET Server] OBVIOUS
                    <5> HIDE DEF F_p
                    <5>2. F' = [F EXCEPT ![p] = F_p] BY DEF ReceiveFAIL, F_p
                    <5> QED BY <5>1, <5>2, FunctionExcept
                <4>3. g' \in [Server -> [Server -> DigraphType(Server)]]
                    <5> DEFINE pi == p
                    <5> DEFINE pj == m.target
                    <5> DEFINE pk == m.owner
                    <5> DEFINE PruneAllFaulty(p_star, tg) == 
                                     IF \A q \in tg.node : F[pi][q] # {} THEN [node |-> {}, edge |-> {}] ELSE tg
                    <5> DEFINE g_p == [p_star \in Server |-> 
                                IF pj \notin g[pi][p_star].node THEN g[pi][p_star] 
                                ELSE PruneAllFaulty(p_star, TrackingDigraph(pi, p_star))']
                    <5> g' = [g EXCEPT ![p] = g_p] BY DEF ReceiveFAIL
                    <5> HIDE DEF PruneAllFaulty, g_p
                    <5> SUFFICES g_p \in [Server -> DigraphType(Server)]
                         BY FunctionExcept DEF DeliverMessage, ReceiveFAIL 
                    <5> SUFFICES ASSUME NEW p_star \in Server
                                 PROVE g_p[p_star] \in DigraphType(Server)
                        BY FunctionExcept DEF g_p
                    <5>1. CASE pj \notin g[pi][p_star].node
                        BY <5>1 DEF g_p, DigraphType
                    <5>2. CASE pj \in g[pi][p_star].node
                        <6> SUFFICES PruneAllFaulty(p_star, TrackingDigraph(pi, p_star))' \in DigraphType(Server)
                            BY <5>2 DEF g_p
                        <6> DEFINE updated_tg == TrackingDigraph(pi, p_star)'
                        <6> HIDE DEF updated_tg
                        <6> SUFFICES updated_tg \in DigraphType(Server)
                            BY <5>2 DEF PruneAllFaulty, updated_tg, DigraphType
                        <6> DEFINE successor(q) == Successors(G, q) \ F'[pi][q]    
                        <6> DEFINE edges == {e \in Server \X Server : F'[pi][e[1]] # {} /\ e[2] \in successor(e[1])}
                        <6> DEFINE tg_nodes == {srv \in Server : AreConnectedViaFailures(p_star, srv, [node |-> Server, edge |-> edges], F'[pi])}
                        <6> DEFINE tg_edges == {e \in tg_nodes \X tg_nodes : F'[pi][e[1]] # {} /\ e[2] \in successor(e[1])} 
                        <6> SUFFICES [node |-> tg_nodes, edge |-> tg_edges] \in DigraphType(Server)
                            BY DEF updated_tg, TrackingDigraph
                        <6> HIDE DEF tg_edges, tg_nodes, edges, successor
                        <6> SUFFICES tg_nodes \in SUBSET Server
                            BY DEF DigraphType, tg_edges                           
                        <6> QED BY DEF tg_nodes                    
                    <5> QED BY <5>1, <5>2                
                 <4> QED BY <2>1, <2>2, <4>1, <4>2, <4>3 DEF DeliverMessage, ReceiveFAIL
            <3>2. CASE m.owner \in F[p][m.target]
                BY <2>1, <2>2, <3>2 DEF DeliverMessage, ReceiveFAIL
            <3> QED BY <3>1, <3>2               
          <2>5. CASE (recvMsg'.type # "BCAST" /\ recvMsg'.type # "FAIL")
            BY <2>1, <2>2, <2>5 DEF DeliverMessage
          <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5
    (* Prove that the TypeInvariant is preserved by Adeliver(p) *)
    <1>5. ASSUME TypeInvariant, NEW p \in Server, Adeliver(p) 
          PROVE TypeInvariant'  
        <2> USE TypeInvariant,  Adeliver(p) DEF TypeInvariant, NetTypeInvariant, Adeliver
        <2>1. flag'.done[p] = 1 OBVIOUS
        <2> QED BY <2>1  
    (* Prove that the TypeInvariant is preserved by Fail(p) *)
    <1>6. ASSUME TypeInvariant, NEW p \in Server, Fail(p) 
          PROVE TypeInvariant'
        <2> USE TypeInvariant,  Fail(p) DEF TypeInvariant, NetTypeInvariant, Fail
        <2>1. flag'.nonFaulty[p] = 0 OBVIOUS
        <2> QED BY <2>1  
    (* Prove that the TypeInvariant is preserved by DetectFailure(pj,pk) *)
    <1>7. ASSUME TypeInvariant, NEW pj \in Server, 
                                NEW pk \in Server, 
                                DetectFailure(pj,pk)
          PROVE TypeInvariant'
        <2> USE TypeInvariant, DetectFailure(pj,pk) DEF TypeInvariant, NetTypeInvariant, DetectFailure
        <2>1. recvBuf' \in [Server -> Seq(Message)] BY DEF Message
        <2>2. FD' \in [Server -> [Server -> {0, 1}]] OBVIOUS
        <2> QED BY <2>1, <2>2               
    <1> QED BY <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 

(* Prove that the type invariant is preserved by the specification Spec *) 
THEOREM TypeInv == Spec => []TypeInvariant
    (* Prove stuttering step *) 
    <1>1. TypeInvariant /\ UNCHANGED vars => TypeInvariant' 
        BY DEF TypeInvariant, NetTypeInvariant, vars
    (* Use InitTypeInv and NextTypeInv *)    
    <1> QED BY PTL, InitTypeInv, NextTypeInv, <1>1 DEF Spec
     
=============================================================================