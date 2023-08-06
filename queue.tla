---- MODULE queue ----

EXTENDS Integers, Sequences, FiniteSets
CONSTANT tasks, number_of_processors, queue_size_bound
VARIABLE queue, running_tasks

enumerable_sequence (some_set, length_bound) == UNION { [1 .. length -> some_set] : length \in 0 .. length_bound }

range_of_sequence (given_sequence) == {given_sequence [index] : index \in DOMAIN given_sequence}

enumerate_set (given_set) ==
              LET enumerate_set_function [given_subset \in SUBSET given_set] ==
                  IF given_subset = { }
                  THEN <<>>
                  ELSE LET element == CHOOSE element \in given_subset : element = element
                       IN <<element>> \o enumerate_set_function [given_subset \ {element}]
              IN enumerate_set_function [given_set]

type_invariant ==
               /\ queue \in [queued_tasks : enumerable_sequence (tasks, queue_size_bound), number_of_running_tasks : Nat]
               /\ running_tasks \in SUBSET tasks

properties ==
               /\ range_of_sequence (enumerate_set (range_of_sequence (queue.queued_tasks))) = range_of_sequence (queue.queued_tasks) (* Delete this once I am sure this law holds? *)

initial_state ==
              /\ running_tasks = { }
              /\ queue = [queued_tasks |-> <<>>, number_of_running_tasks |-> 0]

some_tasks_ended ==
            \E ending_tasks \in SUBSET (running_tasks) :
              \E prefix_of_queued_tasks \in enumerable_sequence (tasks, queue_size_bound), suffix_of_queued_tasks \in enumerable_sequence (tasks, queue_size_bound) :
                 /\ queue.queued_tasks = prefix_of_queued_tasks \o suffix_of_queued_tasks
                 /\ Len (prefix_of_queued_tasks) <= Cardinality (ending_tasks)
                 /\ (* We want to make sure that we queue as many tasks as we can. *)
                     \/ (Len (prefix_of_queued_tasks) + Cardinality (running_tasks) <= number_of_processors /\ Len (suffix_of_queued_tasks) = 0)
                     \/ (Len (prefix_of_queued_tasks) + Cardinality (running_tasks) = number_of_processors /\ Len (suffix_of_queued_tasks) > 0)
                 /\ queue' = [queue EXCEPT !.queued_tasks = suffix_of_queued_tasks, !.number_of_running_tasks = @ - Cardinality (ending_tasks)]
                 /\ running_tasks' = (running_tasks \ ending_tasks) \union range_of_sequence (prefix_of_queued_tasks)

tasks_added (given_tasks) ==
  /\ range_of_sequence (enumerate_set (given_tasks)) = given_tasks (* Delete this once I am sure this law holds? *)
  /\
            \E tasks_to_run \in SUBSET tasks, tasks_to_queue \in SUBSET tasks :
                /\ given_tasks = tasks_to_run \union tasks_to_queue
                /\ tasks_to_run \intersect tasks_to_queue = { }
                /\ given_tasks \intersect (running_tasks \union range_of_sequence (queue.queued_tasks)) = { }
                /\ Len (queue.queued_tasks) + Cardinality (tasks_to_queue) < queue_size_bound
                /\ (* We want to make sure that we queue as many tasks as we can. *)
                    \/ (Cardinality (tasks_to_run) + Cardinality (running_tasks) <= number_of_processors /\ Cardinality (tasks_to_queue) = 0)
                    \/ (Cardinality (tasks_to_run) + Cardinality (running_tasks) = number_of_processors /\ Cardinality (tasks_to_queue) > 0)
                /\ queue' = [queue EXCEPT !.queued_tasks = @ \o enumerate_set (tasks_to_queue), !.number_of_running_tasks = @ + Cardinality (tasks_to_run)]
                /\ running_tasks' = running_tasks \union tasks_to_run

next_state == some_tasks_ended \/ \E some_tasks \in SUBSET tasks : tasks_added (some_tasks)

specification == initial_state /\ [][next_state]_<<queue, running_tasks>>

invariant ==
          /\ Cardinality (running_tasks) <= number_of_processors (* Safety. *)
          /\ Len (queue.queued_tasks) > 0 => Cardinality (running_tasks) = number_of_processors (* Efficiency. *)

====