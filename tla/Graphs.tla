(* 
 * Copyright (c) 2016 HLRS, University of Stuttgart. All rights reserved.
 * 
 * Author(s): Marius Poke <marius.poke@hlrs.de>
 *)
------------------------------- MODULE Graphs ------------------------------- 
(***************************************************************************)
(* Source: Leslie Lamport, Specifying Systems: The TLA+ Language and Tools *) 
(* for Hardware and Software Engineers, 2002                               *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, ExactSeqs

LOCAL INSTANCE TLC

DigraphType(S) == \* A directed graph with nodes in set S
    [node : SUBSET S, edge : SUBSET (S \X S)]

IsDirectedGraph(G) ==
   /\ G = [node |-> G.node, edge |-> G.edge]
   /\ G.edge \subseteq (G.node \X G.node)

DirectedSubgraph(G) ==    
  {H \in  DigraphType(G.node) : IsDirectedGraph(H) /\ H.edge \subseteq G.edge}
-----------------------------------------------------------------------------

Max(a,b) == IF a > b THEN a ELSE b

Successors(G,p) == \* p's successors in G
    {q \in G.node : <<p, q>> \in G.edge}
Predecessors(G,p) == \* p's predecessors in G
    {q \in G.node : <<q, p>> \in G.edge}
NodeInDegree(G,p) == 
    Cardinality(Successors(G,p))
NodeOutDegree(G,p) == 
    Cardinality(Predecessors(G,p))
NodeDegree(G,p) == 
    Max(NodeInDegree(G,p),NodeOutDegree(G,p))
GraphDegree(G) ==
    CHOOSE d \in 0 .. Cardinality(G.node) : 
                       /\ (\E p \in G.node : d = NodeDegree(G,p)) 
                       /\ (\A q \in G.node : d \geq NodeDegree(G,q))
    
IsGraphRegular(G) ==
    /\ \A p \in G.node : NodeInDegree(G,p) = NodeOutDegree(G,p)
    /\ \A p,q \in G.node : NodeInDegree(G,p) = NodeInDegree(G,q)
    
    
AdjustEdgeInDigraph(G) ==  \* remove edges that do not connect two nodes
   [G EXCEPT !.edge = G.edge \ {e \in G.edge : e[1] \notin G.node \/ e[2] \notin G.node}]       

-----------------------------------------------------------------------------

  
(* Use AreConnectedTLAPS in TLAPS to avoid recursive functions *)
Path(G) == 
    {p \in Seq(G.node) :
         /\ p # << >>
         /\ \A i \in 1..(Len(p)-1) : <<p[i], p[i+1]>> \in G.edge}
AreConnectedTLAPS(m, n, G) == 
    \/ m = n
    \/ \E p \in Path(G) : (p[1] = m) /\ (p[Len(p)] = n)
    
AreConnectedViaFailures(m, n, G, FS) == 
    \/ m = n
    \/ \E p \in Path(G) : /\ (p[1] = m) 
                          /\ (p[Len(p)] = n) 
                          /\ (\A i \in 1..Len(p)-1 : FS[p[i]] # {})
    
(* Set of loopless paths from u to v in digraph G *)    
PathsFromTo(G, u, v) == 
    {p \in Path(G) : /\ p[1] = u 
                     /\ p[Len(p)] = v
                     /\ \A i,j \in 1..Len(p) : p[i] = p[j] => i = j}

(* Definition of node disjoing *)                     
NodeDisjoint(P, Q) ==
    \A i \in 2..Len(P), j \in 2..Len(Q) : P[i] # Q[j]                     
                     
(* Set of node-disjoing paths from u to v in digraph G *)    
NodeDisjPathsFromTo(G, u, v) ==
    CHOOSE paths \in SUBSET PathsFromTo(G, u, v) : \A P, Q \in paths : NodeDisjoint(P, Q) 
  
AreConnected(u, v, G) == \* check whether two nodes are connected, i.e., BFS
    \*/\ Print([op |-> "AreConnected", args |-> <<u, v, G>>], TRUE)
    /\ LET fun[Q \in Seq(G.node), visited \in [G.node -> {0,1}]] ==
            \*/\ Print([queue |-> Q, done_flag |-> done], TRUE) 
            /\ IF Q = << >> THEN FALSE \* Couldn't reach v from u in G
               ELSE LET w == Head(Q) \* next vertex
                    IN IF w = v THEN TRUE \* Reached v; done
                       ELSE fun[Tail(Q) \o ExactSeqFor({x \in Successors(G, w): visited[x] # 1}), \* add not visited successors 
                                    [visited EXCEPT ![w] = 1]]
       IN fun[<<u>>, [w \in G.node |-> IF w = u THEN 1 ELSE 0]] 
        

IsStronglyConnected(G) == 
  \A m, n \in G.node : AreConnected(m, n, G)
  
-----------------------------------------------------------------------------
  
(* G has at least f+1 nodes, i.e., |G| > f, and 
   any subgraph H with at leat |G|-f nodes is strongly connected,
   i.e., (|H| >= |G| - f) => IsStronglyConnected(H)
*)
IsGraphFaultTolerant(G,f) ==
  /\ Cardinality(G.node) > f   
  /\ \A H \in DirectedSubgraph(G) : 
    (Cardinality(H.node) \geq Cardinality(G.node) - f) => IsStronglyConnected(H)

=============================================================================
