---- MODULE  CommunityModules----
EXTENDS TLC, Integers, Sequences

CSV == INSTANCE CSV

TEST == CSV!CSVWrite("%1$s#%2$s#%3$s", <<"abc", 42, {"x", "y"} >>, "csv-out.csv")
(*--algorithm CommunityModules

begin
    assert TEST;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a0f7b67a" /\ chksum(tla) = "b924e267")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(TEST, "Failure of assertion at line 10, column 5.")
         /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
