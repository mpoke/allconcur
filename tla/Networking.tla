(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE Networking ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, Graphs, ExactSeqs

LOCAL INSTANCE TLC

CONSTANTS Server,  \* set of servers identifiers
          G, \* overlay network
          Message \* set of existing messages 

(*
 * sendBuf[i] pi's sending buffer
 * recvBuf[i] pi's receiving buffer 
 *)
 VARIABLES sendBuf, recvBuf, recvMsg

\* ASSUMPTION: G is a regular digraph
ASSUME IsDirectedGraph(G)  

------------------------------------------------------------------------------          
NetInit == \* The initial predicate
    /\ sendBuf = [p \in Server |-> << >> ]
    /\ recvBuf = [p \in Server |-> << >> ]
    /\ recvMsg = CHOOSE m \in Message : TRUE    \* initial value is irrelevant (avoid multiple init states)
    
NetTypeInvariant == \* The type invariant
    /\ sendBuf \in [Server -> Seq(Message \X Seq(Server))]
    /\ recvBuf \in [Server -> Seq(Message)]
    /\ recvMsg \in Message
    
------------------------------------------------------------------------------

Debug(obj) ==
    /\ TRUE
    \*/\ Print(obj, TRUE)
Info(obj) ==
    /\ TRUE
    \*/\ Print(obj, TRUE)

(* p sends message m to all nonFaulty successors (except m's owner):
 *   add a tuple <<m, {servers_to_send_to}>> to the send buffer
 * Note: SendMessage(p, m) is not checking whether the message was already sent 
 *)
SendMessage(p, msgs, nonFaulty) == \* p sends each message in msgs  
    /\ LET SendTo(i) == {q \in Successors(G,p) \ {msgs[i].owner} : nonFaulty[q] = 1}
           buf == [i \in 1..Len(msgs) |-> <<msgs[i], ExactSeqFor(SendTo(i))>>]
       IN sendBuf' = [sendBuf EXCEPT ![p] = sendBuf[p] \o buf]
    /\ Debug([op |-> "SendMessage", args |-> <<p, msgs, nonFaulty>>])
    
NetTXMessage(p) ==   \* p sends the next message from the send buffer to one of its successor
    LET msg == Head(sendBuf[p])[1] \* message to be sent
        succ == Head(sendBuf[p])[2] \* list of successors (not yet sent to)
    IN  \* enabled only if...
        /\ sendBuf[p] # << >> \* ...sendBuf[p] is nonempty
        /\ IF succ = << >> THEN /\ sendBuf' = [sendBuf EXCEPT ![p] = Tail(sendBuf[p])]  \* no more successors; remove message
                                /\ UNCHANGED <<recvBuf>>
           ELSE LET next == Head(succ)
                    sendBuf_p_head == [sendBuf[p][1] EXCEPT ![2] = Tail(succ)]
                    sendBuf_p == [sendBuf[p] EXCEPT ![1] = sendBuf_p_head]                    
                IN /\ recvBuf' = [recvBuf EXCEPT ![next] = Append(recvBuf[next], msg)]
                   /\ sendBuf' = [sendBuf EXCEPT ![p] = sendBuf_p] \* remove successor 
     
DeliverMessage(p) == \* p delivers a message from recvBuf
    \* enabled only if...
    /\ recvBuf[p] # << >> \* ...receive bufffer is nonempty
    /\ recvMsg' = Head(recvBuf[p])
    /\ recvBuf' = [recvBuf EXCEPT ![p] = Tail(recvBuf[p])]
        
==============================================================================