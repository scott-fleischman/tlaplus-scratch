---- MODULE BoundedFIFO ----
EXTENDS Naturals, Sequences
CONSTANT Message, N
VARIABLES in, out
ASSUME (N \in Nat) /\ (N > 0)

Inner(q) == INSTANCE InnerFIFO

BNext(q) ==
  /\ Inner(q)!Next
  /\ Inner(q)!BufRcv => (Len(q) < N)

Spec == \E q : Inner(q)!Init /\ [][BNext(q)]_<<in,out,q>>

====
