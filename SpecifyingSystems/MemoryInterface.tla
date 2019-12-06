---- MODULE MemoryInterface ----
VARIABLE memInt
CONSTANTS
  Send(_,_,_,_), \* Send(p,d,_,_) represents processor 'p' sending value 'd' to the memory
  Reply(_,_,_,_), \* Reply(p,d,_,_) represents the memory sending valud 'd' to processor 'p'
  InitMemInt, \* The possible initial values of memInt
  Proc, \* The set of processor identifiers
  Adr, \* The set of memory addresses
  Val \* The set of possible memory values that can be assigned to an address
ASSUME \A p, d, miOld, miNew :
  /\ Send(p, d, miOld, miNew) \in BOOLEAN 
  /\ Reply(p, d, miOld, miNew) \in BOOLEAN 

ReadRequest == [op: {"Rd"}, adr: Adr]
WriteRequest == [op: {"Wt"}, adr: Adr, val: Val]
MReq == ReadRequest \union WriteRequest

NoVal == CHOOSE v : v \notin Val

====
