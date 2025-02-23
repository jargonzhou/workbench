---- MODULE squares ----
\* https://github.com/tlaplus/vscode-tlaplus/wiki/Getting-Started

EXTENDS TLC, Integers

(*--algorithm squares
variables
    x \in 1..10;

begin
    \* assert x ^ 2 <= 100;
    assert x ^ 2 <= 99; \* make model check fail
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b443faf4" /\ chksum(tla) = "4de2cd65")
VARIABLES pc, x

vars == << pc, x >>

Init == (* Global variables *)
        /\ x \in 1..10
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x ^ 2 <= 99, "Failure of assertion at line 12, column 5.")
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
