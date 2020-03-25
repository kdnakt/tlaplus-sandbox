------------------------------ MODULE Transfer ------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10, money = 5;

begin
A: alice_account := alice_account - money;
B: bob_account := bob_account + money;

end algorithm *)

=============================================================================
\* Modification History
\* Last modified Wed Mar 25 09:15:47 JST 2020 by akito
\* Created Wed Mar 25 09:15:22 JST 2020 by akito
