----- MODULE HourClock ----
EXTENDS Naturals
VARIABLE hr
HCini == hr \in (1..12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
-----
THEOREM HC => []HCini
-----
HCnxt2 == hr' = (hr % 12) + 1
HC2 == HCini /\ [][HCnxt2]_hr
=====
