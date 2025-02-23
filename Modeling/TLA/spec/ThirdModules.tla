---- MODULE ThirdModules ----
EXTENDS TLC

PT == INSTANCE PT

(**--algorithm ThirdModules
variables pair = <<1,2>>
begin
    assert PT!Max(pair[1], pair[2]) = 2
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f2cd4c8c" /\ chksum(tla) = "eacc5b56")
VARIABLES pc, pair

vars == << pc, pair >>

Init == (* Global variables *)
        /\ pair = <<1,2>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(PT!Max(pair[1], pair[2]) = 2, 
                   "Failure of assertion at line 9, column 5.")
         /\ pc' = "Done"
         /\ pair' = pair

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
