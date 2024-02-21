Require Import String.

Open Scope string_scope.

Ltac test_success := idtac "--- OK".

Ltac test_failure := 
  idtac " ";
  idtac "========================" ;
  idtac "===== Test Failed. =====" ;
  idtac "========================" ;
  idtac " ".

Ltac tested_tactic n :=
  idtac "* Tactic tested :" n.

Ltac test_case n :=
  idtac "** Test case :" n .

