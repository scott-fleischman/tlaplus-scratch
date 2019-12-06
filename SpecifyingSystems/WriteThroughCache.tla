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

DoRd(p) == \* Perform a read by p of a value in its cache
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] /= NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

DoWr(p) == \* Write to p's cache, update other caches, and enqueue memory update
  LET r == buf[p]
  IN  /\ (ctl[p] = "busy") /\ (r.op = "Wr")
      /\ Len(memQ) < QLen
      /\ cache' =
          [q \in Proc |->
            IF (p = q) \/ (cache[q][r.adr] /= NoVal)
              THEN [cache[q] EXCEPT ![r.adr] = r.val]
              ELSE cache[q]]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

vmem == \* The value wmem will have after all the writes in memQ are performed
  LET f[i \in 0..Len(memQ)] ==
        IF i = 0
          THEN wmem
          ELSE IF memQ[i][2].op = "Rd"
                THEN f[i - 1]
                ELSE [f[i - 1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN f[Len(memQ)]

MemQWr == \* Perform write at head of memQ to memory
  LET r == Head(memQ)[2]
  IN  /\ (memQ /= <<>>) /\ (r.op = "Wr")
      /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == \* Perform an enqueued read to memory
  LET p == Head(memQ)[1] \* The requesting processor
      r == Head(memQ)[2] \* The request at the head of memQ
  IN  /\ (memQ /= <<>>) /\ (r.op = "Rd")
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<memInt, wmem, buf, ctl>>

Evict(p, a) == \* Remove address 'a' from p's cache.
  /\ (ctl[p] = "waiting") => (buf[p].adr /= a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc :
      \/ Req(p) \/ Rsp(p)
      \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
      \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr \/ MemQRd

Spec == Init /\ [][Next]_<<memInt, wmem, buf, ctl, cache, memQ>>

----
THEOREM Spec => [](TypeInvariant /\ Coherence)
----
LM == INSTANCE Memory
THEOREM Spec => LM!Spec

====
