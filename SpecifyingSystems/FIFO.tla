---- MODULE FIFO ----
CONSTANT Message
VARIABLES in, out

Inner(q) == INSTANCE InnerFIFO
Spec == \E q : Inner(q)!Spec
====
