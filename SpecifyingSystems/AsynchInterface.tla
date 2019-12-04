---- MODULE AsynchInterface ----
EXTENDS Naturals

CONSTANT Data
VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

TypeInvariant ==
  /\ val \in Data
  /\ rdy \in {0,1}
  /\ ack \in {0,1}

Init ==
  /\ val \in Data
  /\ rdy \in {0,1}
  /\ ack = rdy

Send ==
  /\ ack = rdy
  /\ val' \in Data
  /\ rdy' = 1 - rdy
  /\ UNCHANGED ack

Rcv ==
  /\ ack /= rdy
  /\ ack' = 1 - ack
  /\ UNCHANGED <<val, rdy>>

Next ==
  \/ Send
  \/ Rcv

Spec == Init /\ [][Next]_vars
====
