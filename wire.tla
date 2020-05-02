---- MODULE wire ----

EXTENDS Integers

(*
--algorithm wire
variables
    people = {"Alice", "Robert"},
    account = [person \in people |-> 5],


define
    NoOverdrafts == \A person \in people: account[person] >= 0
end define;

process Wire \in 1..3

    variables
        sender = "Alice",
        receiver = "Robert",
        amount \in 1..account[sender];

    begin
        Withdraw: account[sender] := account[sender] - amount;
        Deposit: account[sender] := account[sender] + amount;
    end process;

end algorithm;
*)

====