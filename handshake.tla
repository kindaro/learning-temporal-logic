---- MODULE handshake ----
EXTENDS Naturals
CONSTANT data
example_data == {"a", "b", "c", "d"}
VARIABLE channel

type_invariant == channel \in [value : data, ready : {0, 1}, acknowledge : {0, 1}]

initial == type_invariant /\ channel.ready = channel.acknowledge

send (given_value) ==
     /\ channel.ready = channel.acknowledge
     /\ channel' = [channel EXCEPT !.value = given_value, !.ready = 1 - @]

receive ==
        /\ channel.ready # channel.acknowledge
        /\ channel' = [channel EXCEPT !.acknowledge = 1 - @]

next ==
     \/ \E some_value \in data : send (some_value)
     \/ receive

specification == initial /\ [][next]_<<channel>>
====