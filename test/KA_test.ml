open OUnit2
open KA_equiv.KA.KAParser
open KA_equiv.KA

let fromStr str = Option.get (parse_reg str)

let epsilon_tests = "epslion test" >:::[
  "ϵ(a*) = 1" >:: (fun _ ->
    assert_equal true (epsilon (fromStr "a*")));
  "ϵ(a) = 0" >:: (fun _ -> 
    assert_equal false (epsilon (fromStr "a")));
]

let deriv_test = "deriv test" >::: [
  "Dₐ(a + b) = 1 + 0" >:: (fun _ ->
    assert_equal ~printer: pprint 
      (fromStr "1 + 0") (deriv 'a' (fromStr "a + b")));
]