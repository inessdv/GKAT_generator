open OUnit2
open KA_equiv.KAT_Set.Parser
open KA_equiv.KAT_Set
open KA_equiv.Common
open KA_equiv.KAT_Set.Print

let fromStr str = (parse_kat_unsafe str)

let epsilon_tests = "epslion test" >:::[
  "ϵ(b)(bpc) = 0" >:: (fun _ ->
    assert_equal false (epsilon (Atom.of_list ["b";"c"]) (fromStr "b(p(c))")));  (* p* contains all atoms *) (* p+b contains all atoms*)
  "ϵ((b -c),(bpc)) = 0" >:: (fun _ -> 
    assert_equal false (epsilon (Atom.of_list ["b"]) (fromStr "b(p(c))")));
]

let deriv_test = "deriv and linearization test" >::: [
  "D(ap)((ap+bq) = 1+0" >:: (fun _ ->
    let exp = fromStr "a(p) + b(q)" in 
    assert_equal ~printer: pprint_sum
      (KATSet.singleton(fromStr "1+0")) 
      (deriv (Atom.of_list ["a";"b"],"p") (get_der_map (PBoolSet.of_list ["a"; "b"]) (exp))));
]
let equiv_test = "equivalence test" >::: [
  "equiv (b+1) (1)" >:: (fun _ ->
    assert_equal true
      (equiv (fromStr "b1 + 1") (fromStr "1") ));
      
]



(* let linearization_test = "linearization test" >::: [
  "D(bcp)((b+p)p) = p + 1" >:: (fun _ ->
    assert_equal ~printer: pprint 
      (fromStr "p + 1") (deriv 'a' (fromStr "a + b")));
] *)

(* let deriv_test = "equiv test" >::: [
  "D(bcp)((b+p)p) = p + 1" >:: (fun _ ->
    assert_equal ~printer: pprint_sum
      (KATSet.singleton(fromStr "1+0")) (deriv (Atom.of_list ["a";"b"],"p") (linearization (fromStr "ap + bq"))));
] *)