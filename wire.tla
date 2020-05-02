---- MODULE wire ----

EXTENDS Integers

(*
--algorithm wire
variables
    people = {"Alice", "Robert"},
    account = [person \in people |-> 5],


define
    NoOverdrafts == \A person \in people: account[person] >= 0
    EventuallyConsistent == <>[] (account["Alice"] + account["Robert"] = 10)
end define;

process Wire \in 1..3

    variables
        sender = "Alice",
        receiver = "Robert",
        amount \in 1..account[sender];

    begin
        Transaction:
            if amount <= account[sender]
            then
                account[sender] := account[sender] - amount;
                Deposit: account[sender] := account[sender] + amount;
            end if;
    end process;

end algorithm;
*)

====