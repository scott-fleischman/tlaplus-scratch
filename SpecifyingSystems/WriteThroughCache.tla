---- MODULE WriteThroughCache ----
EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES wmem, ctl, buf, cache, memQ
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)

M == INSTANCE InternalMemory WITH mem <- wmem
----
Init ==
  /\ M!IInit
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = <<>>

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \union Val \union {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \union {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)

Coherence == \* asserts that if two processors' caches both have copies of an address, then those copies have equal values
  \A p, q \in Proc, a \in Adr :
    (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache [q][a])

----

Req(p) == \* Processor p issues a request
  /\ M!Req(p)
  /\ UNCHANGED <<cache, memQ>>

Rsp(p) == \* The system issues a response to processor p
  /\ M!Rsp(p)
  /\ UNCHANGED <<cache, memQ>>

RdMiss(p) == \* Enqueue a request to write value from memory to p's cache
  /\ (ctl[p] = "busy") /\ (buf[p].op = "Rd")
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

DoRd == \* Perform a read by p of a value in its cache
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] /= NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

====
