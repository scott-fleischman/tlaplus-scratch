---- MODULE AsynchInterface ----
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
  /\ \E data \in Data : val' = data
  /\ rdy' = IF rdy = 0 THEN 1 ELSE 0
  /\ UNCHANGED ack

Ack ==
  /\ ack /= rdy
  /\ ack' = rdy
  /\ UNCHANGED <<val, rdy>>

Next ==
  \/ Send
  \/ Ack

Spec == Init /\ [][Next]_vars
====
