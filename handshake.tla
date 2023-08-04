---- MODULE handshake ----
EXTENDS Naturals
CONSTANT data
example_data == {"a", "b", "c", "d"}
VARIABLE value, ready, acknowledge

type_invariant ==
               /\ value \in data
               /\ ready \in {0, 1}
               /\ acknowledge \in {0, 1}

initial ==
        /\ value \in data
        /\ ready = 0
        /\ acknowledge = 0

send ==
     /\ ready = acknowledge
     /\ value' \in data
     /\ ready' = 1 - ready
     /\ UNCHANGED acknowledge

receive ==
        /\ ready /= acknowledge
        /\ acknowledge' = 1 - acknowledge
        /\ UNCHANGED <<value, ready>>

next == send \/ receive
specification == initial /\ [][next]_<<value, ready, acknowledge>>
====