
Ltac test_success := idtac "Test succeeded.".
Ltac test_failure := 
  idtac " ";
  idtac "========================" ;
  idtac "===== Test Failed. =====" ;
  idtac "========================" ;
  idtac " ".

