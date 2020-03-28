------------------------------ MODULE Transfer ------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money \in 1..20,
          account_total = alice_account + bob_account;

begin
Transfer:
  if alice_account >= money then
    A: alice_account := alice_account - money;
    B: bob_account := bob_account + money;
end if;
C: assert alice_account >= 0;
end algorithm *)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, account_total, pc

vars == << alice_account, bob_account, money, account_total, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ account_total = alice_account + bob_account
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "A"
                  ELSE /\ pc' = "C"
            /\ UNCHANGED << alice_account, bob_account, money, account_total >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money, account_total >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << alice_account, money, account_total >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 14, column 4.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money, account_total >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Transfer \/ A \/ B \/ C
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

MoneyNotNegative == money >= 0
MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Sat Mar 28 10:27:56 JST 2020 by akito
\* Created Wed Mar 25 09:15:22 JST 2020 by akito
