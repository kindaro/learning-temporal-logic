---- MODULE fifo ----
EXTENDS Naturals, Sequences
CONSTANT messages, queue_size_bound
example_messages == {"a", "b", "c", "d"}
VARIABLE input, output, queue
input_channel == INSTANCE handshake WITH data <- messages, channel <- input
output_channel == INSTANCE handshake WITH data <- messages, channel <- output

type_invariant ==
               /\ input_channel!type_invariant
               /\ output_channel!type_invariant
               /\ queue \in Seq (messages)
               /\ queue_size_bound \in Nat

initial ==
        /\ input_channel!initial
        /\ output_channel!initial
        /\ queue = << >>

sender_sends (message) ==
             /\ input_channel!send (message)
             /\ UNCHANGED <<queue, output>>

queue_receives ==
               /\ Len (queue) < queue_size_bound
               /\ input_channel!receive
               /\ queue' = Append (queue, input.value)
               /\ UNCHANGED output

queue_sends ==
            /\ queue # <<>>
            /\ output_channel!send (Head (queue))
            /\ queue' = Tail (queue)
            /\ UNCHANGED input

receiver_receives ==
                  /\ output_channel!receive
                  /\ UNCHANGED <<input, queue>>

next ==
     \/ \E message \in messages : sender_sends (message)
     \/ queue_receives
     \/ queue_sends
     \/ receiver_receives

specification == initial /\ [] [next]_<<input, output, queue>>
====