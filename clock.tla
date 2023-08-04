---- MODULE clock ----

EXTENDS Naturals
VARIABLE hour
initial_hour == hour \in (1 .. 12)
next_hour == hour' = IF hour = 12 THEN 1 ELSE hour + 1
definition_of_clock == initial_hour /\ [] [next_hour]_hour
-----------------
THEOREM definition_of_clock => [] initial_hour
truth == initial_hour
====