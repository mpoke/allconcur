# AllConcur: TLA+ specifcation and TLAPS proofs 

#### Brief 
A formal specification of AllConcur written in the TLA+ specification language [1] and a formal proof of AllConcur's safety on the basis of the specification.

#### Folder overview
- AllConcur.tla -- main specification (including failure detector)
- Networking.tla -- specification of the networking interface that provides an interface for asynchronous message-based communication
- Graphs.tla -- specification for directed graphs (source: [1])
- TypeInvariant_proofs.tla -- proof of the type invariant
- AllConcur_proofs.tla -- proof of AllConcur's safety
- TrackingDigraph.tla -- tracking digraphs specification and proofs
- ReconstructedTD.tla -- reconstructed tracking digraphs specification and proofs
- FD_proofs.tla -- proof of accuracy for failure detector
- ExactSeqs.tla -- create a sequence out of a set (source: [2])
- ExactSeqs_proofs.tla -- facts about sequences (source: [2])
- Naturals_proofs.tla -- facts about naturals (source: [2])

Create a sequence out of a set                                          *)
(* Source: Rodeheffer TL. The Naiad clock protocol: Specification, model   *) 
(* checking, and correctness proof. Tech. Rep. MSR-TR-2013-20, Microsoft   *)
(* Research, Redmond (Feb 2013)  

#### References

[1] L. Lamport: *Specifying Systems: The TLA+ Language and Tools for Hardware and Software Engineers*, Addison-Wesley Longman Publishing Co., Inc., Boston, MA, USA, 2002
[2] Rodeheffer TL: *The Naiad clock protocol: Specification, model checking, and correctness proof*, Tech. Rep. MSR-TR-2013-20, Microsoft Research, Redmond, Feb 2013.
