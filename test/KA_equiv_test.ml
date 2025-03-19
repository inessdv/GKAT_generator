open OUnit2

let _ =
  run_test_tt_main
    ("all tests"
    >::: [
           KA_test.epsilon_tests;
           KA_test.deriv_test;
           KAT_test.epsilon_tests;
           KAT_test.deriv_test;
           GKAT_test_qcheck.test_equiv_deriv; 
           GKAT_test_qcheck.test_equiv_aut;
           GKAT_test_qcheck.test_aut_vs_deriv;
           GKAT_test_qcheck.test_equiv_symb;
           GKAT_test_qcheck.test_symb_vs_gkat; 
           GKAT_test_qcheck.test_symb_vs_aut
  ])
