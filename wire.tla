---- MODULE wire ----

EXTENDS Integers

(*
--algorithm wire
variables
    people = {"Alice", "Robert"},
    account = [person \in people |-> 5],

    sender = "Alice",
    receiver = "Robert",
    amount = 3;

define
    NoOverdrafts == \A person \in people: account[person] >= 0
end define;

begin
    Withdraw: account[sender] := account[sender] - amount;
    Deposit: account[sender] := account[sender] + amount;
end algorithm;
*)

====