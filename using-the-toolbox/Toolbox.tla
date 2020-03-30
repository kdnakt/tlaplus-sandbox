------------------------------ MODULE Toolbox ------------------------------
EXTENDS Integers

(* --algorithm example
variables x = 5
begin
 Add:
  x := x + 1;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 5
        /\ pc = "Add"

Add == /\ pc = "Add"
       /\ x' = x + 1
       /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Add
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Tue Mar 31 08:53:44 JST 2020 by akito
\* Created Tue Mar 31 08:53:16 JST 2020 by akito
