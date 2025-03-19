open QCheck2
open KA_equiv
module GKAT_Symb = GKAT_Symb_BDD

(*
let exp_max_size = 6000
let bexp_max_size = 30
let max_p_bool_count = 200
let bench_count_eq = 50
(*let counter_rand = ref 0*)
let counter_equal = ref 0
let path = "../e3000b30p200"
*)

(* To execute the generator main should take in 5 variable
1: exp_max_size
2: bexp_max_size
3: max_p_bool_count
4: bench_count_eq
5: bench_count_ne
6: counter_equal
7: counter_rand
8: path
*)

(*let bench_count_ne = int_of_string Sys.argv.(5)*)
(*let counter_rand = ref (int_of_string Sys.argv.(7))*)

let exp_max_size = int_of_string Sys.argv.(1)
let bexp_max_size = int_of_string Sys.argv.(2)
let max_p_bool_count = int_of_string Sys.argv.(3)
let bench_count_eq = int_of_string Sys.argv.(4)
let counter_equal = ref (int_of_string Sys.argv.(5))
let path = Sys.argv.(6)

  
(*
let mk_rand_fmt () =
  let path = Fmt.str "%sne/exp%02d.txt" path !counter_rand in
  incr counter_rand;
  let ch = open_out path in
  (ch, Format.formatter_of_out_channel ch)
*)
let mk_equiv_fmt () =
  let path = Fmt.str "%seq/exp%02d.txt" path !counter_equal in
  incr counter_equal;
  let ch = open_out path in
  (ch, Format.formatter_of_out_channel ch)

  module GenExp = struct
    open GKAT_2
  
    let return = Gen.return
    let ( >|= ) = Gen.( >|= )
    let ( let* ) = Gen.( let* )
  
    let p_bool : bExp Gen.t =
      Gen.int_range 1 max_p_bool_count >|= fun n -> PBool ("b" ^ string_of_int n)
  
    let b_exp size : bExp Gen.t =
      Gen.fix
        (fun self size ->
          if size <= 1 then p_bool
          else
            Gen.frequency
              [
                (20, let* b_exp1 = self (size / 2) in
                 let* b_exp2 = self (size / 2) in
                 return @@ And (b_exp1, b_exp2));
                (20, let* b_exp1 = self (size / 2) in
                 let* b_exp2 = self (size / 2) in
                 return @@ Or (b_exp1, b_exp2));
                (1, let* b_exp' = self (size - 1) in
                 return @@ Not b_exp');
              ])
        size
  
    module IntSet = Set.Make (Int)
  
    (** Generate a CF-GKAT expression *)
    (*let exp_sized bexp_size size =
      (* a function that generate a expression and all the labels in the expression,
         represented as ints*)
      (Gen.fix (fun self size ->
           (* all the expression with size 1 *)
           let size_one_lst =
             [
               (1, return @@ test One);
               ( 50,
                 let* p = Gen.small_nat in
                 return @@ Pact ("p" ^ string_of_int p) );
             ]
           in
           (* all the recursive expression generation (not size 1) *)
           let recursive_lst =
             [
               ( 15,
                 let* e1 = self (size / 2) in
                 let* e2 = self (size / 2) in
                 return @@ Seq (e1, e2) );
               ( 3,
                 let* b = b_exp bexp_size in
                 let* e1 = self (size / 2) in
                 let* e2 = self (size / 2) in
                 return @@ If (b, e2, e1) );
               ( 1,
                 let* b = b_exp bexp_size in
                 let* e_loop = self (size - 1) in
                 return @@ While (b, e_loop) );
             ]
           in
           if size <= 1 then Gen.frequency size_one_lst
           else Gen.frequency @@ recursive_lst))
        (* default configuration for generating expressions:
           not in loop, with the input labels as start, and the input size*)
        size*)
  
    (** Generating a pair of random expressions
    
    We do not generate expressions using identity, idempotence, complement rule, because they can be viewed as "trivial"
    We do not generate any Zero, however, many rules can still generate zero expressions.
    These cases will be rare when the maximum number of primitive tests are large. 
    *)
    let gen_eq_bexp size =
      Gen.fix
        (fun self size ->
          if size <= 1 then
            Gen.oneof
              [
                (* reflexivity *)
                (let* b = b_exp size in
                 return @@ (b, b));
              ]
          else
            Gen.frequency
              [
                (* symmetry *)
                (10, let* b1, b2 = self (size - 1) in
                 return @@ (b2, b1));
                (* congurence *)
                (3, let* b1, b2 = self (size - 1) in
                 return (Not b1, Not b2));
                (10, let* b1, b1' = self (size / 2) in
                 let* b2, b2' = self (size / 2) in
                 return (And (b1, b2), And (b1', b2')));
                (10, let* b1, b1' = self (size / 2) in
                 let* b2, b2' = self (size / 2) in
                 return (Or (b1, b2), Or (b1', b2')));
                (* commutativity *)
                (10, let* b1, b1' = self (size / 2) in
                 let* b2, b2' = self (size / 2) in
                 return (Or (b1, b2), Or (b2', b1')));
                (10, let* b1, b1' = self (size / 2) in
                 let* b2, b2' = self (size / 2) in
                 return (And (b1, b2), And (b2', b1')));
                (* Associativity *)
                (10, let* b1, b1' = self (size / 3) in
                 let* b2, b2' = self (size / 3) in
                 let* b3, b3' = self (size / 3) in
                 return (Or (b1, Or (b2, b3)), Or (Or (b1', b2'), b3')));
                (10, let* b1, b1' = self (size / 3) in
                 let* b2, b2' = self (size / 3) in
                 let* b3, b3' = self (size / 3) in
                 return (And (b1, And (b2, b3)), And (And (b1', b2'), b3')));
                (* Identity *)
                (* (let* b1, b1' = self (size - 1) in
                 return (And (b1, One), b1'));
                (let* b1, b1' = self (size - 1) in
                 return (And (One, b1), b1')); *)
                (* (let* b1 = b_exp (size - 1) in
                    return (And (b1, Zero), Zero));
                   (let* b1 = b_exp (size - 1) in
                    return (And (Zero, b1), Zero)); *)
                (* (let* b1, b1' = self (size - 1) in
                 return (Or (b1, Zero), b1'));
                (let* b1, b1' = self (size - 1) in
                 return (Or (Zero, b1), b1'));
                (let* b1 = b_exp (size - 1) in
                 return (Or (b1, One), One));
                (let* b1 = b_exp (size - 1) in
                 return (Or (One, b1), One)); *)
                (* complement *)
                (* (1, let* b1, b2 = self (size / 2) in
                 return (Or (Not b1, b2), One));
                (let* b1, b2 = self (size / 2) in
                 return (And (Not b1, b2), Zero)); *)
                (* idempotence *)
                (* (let* b1, b2 = self (size / 2) in
                 return (Or (b1, b2), b1));
                (let* b1, b2 = self (size / 2) in
                 return (Or (b1, b2), b2));
                (let* b1, b2 = self (size / 2) in
                 return (And (b1, b2), b1));
                (let* b1, b2 = self (size / 2) in
                 return (And (b1, b2), b2)); *)
              ])
        size
  
    (** Generate a pair of equivalent expression
    
    *)
    let gen_eq_exp =
      Gen.fix
        (fun self size ->
          if size <= 1 then
            Gen.frequency
              [
                (* primitive action *)
                ( 100,
                  let* label = Gen.small_nat in
                  return
                    ( Pact ("p" ^ string_of_int label),
                      Pact ("p" ^ string_of_int label) ) );
                (* skip *)
                (1, return (Test One, Test One));
              ]
          else
            Gen.frequency
              [
                (* reflexivity *)
                (* ( 1,
                  let* e = exp_sized bexp_max_size size in
                  return @@ (e, e) ); *)
                (* symmetry *)
                ( 20,
                  let* e1, e2 = self (size - 1) in
                  return @@ (e2, e1) );
                (* equal test *)
                (* (let* b1, b2 = gen_eq_bexp bexp_max_size in
                   return @@ (Test b1, Test b2)); *)
                (* congurence *)
                ( 40,
                  let* e1, e1' = self (size / 2) in
                  let* e2, e2' = self (size / 2) in
                  return @@ (Seq (e1, e2), Seq (e1', e2')) );
                ( 20,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e1, e1' = self (size / 2) in
                  let* e2, e2' = self (size / 2) in
                  return @@ (If (b, e1, e2), If (b', e1', e2')) );
                ( 20,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e, e' = self (size - 1) in
                  return @@ (While (b, e), While (b', e')) );
                (* idempotence *)
                (* ( 2,
                  let* b = b_exp bexp_max_size in
                  let* e, e' = self (size / 2) in
                  return @@ (If (b, e, e'), e) ); *)
                (* skew commutativity *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e1, e1' = self (size / 2) in
                  let* e2, e2' = self (size / 2) in
                  return @@ (If (b, e1, e2), If (Not b', e2', e1')) );
                (* skew assoc *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* c, c' = gen_eq_bexp bexp_max_size in
                  let* e1, e1' = self (size / 3) in
                  let* e2, e2' = self (size / 3) in
                  let* e3, e3' = self (size / 3) in
                  return
                  @@ ( If (c, If (b, e1, e2), e3),
                       If (And (b', c'), e1', If (c, e2', e3')) ) );
                (* guardedness *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e1, e1' = self (size / 2) in
                  let* e2, e2' = self (size / 2) in
                  return @@ (If (b, e1, e2), If (b', Seq (Test b', e1'), e2')) );
                (* right distribute *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e1, e1' = self (size / 3) in
                  let* e2, e2' = self (size / 3) in
                  let* e3, e3' = self (size / 3) in
                  return
                  @@ ( Seq (If (b, e1, e2), e3),
                       If (b', Seq (e1', e3'), Seq (e2', e3')) ) );
                (* associativity *)
                ( 40,
                  let* e1, e1' = self (size / 3) in
                  let* e2, e2' = self (size / 3) in
                  let* e3, e3' = self (size / 3) in
                  return @@ (Seq (e1, Seq (e2, e3)), Seq (Seq (e1', e2'), e3')) );
                (* identities *)
                (* (let* e = exp_sized bexp_max_size (size - 1) in
                    return @@ (Seq (Test Zero, e), Test Zero));
                   (let* e = exp_sized bexp_max_size (size - 1) in
                    return @@ (Seq (e, Test Zero), Test Zero)); *)
                ( 5,
                  let* e, e' = self (size - 1) in
                  return @@ (Seq (Test One, e), e') );
                ( 5,
                  let* e, e' = self (size - 1) in
                  return @@ (Seq (e, Test One), e') );
                (* unrolling *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* e, e' = self (size / 2) in
                  return
                  @@ (While (b, e), If (b', Seq (e', While (b, e')), Test One)) );
                (* tightening *)
                ( 40,
                  let* b, b' = gen_eq_bexp bexp_max_size in
                  let* c, c' = gen_eq_bexp bexp_max_size in
                  let* e, e' = self (size - 1) in
                  return
                  @@ ( While (b, If (c, e, Test One)),
                       While (b', Seq (Test c', e')) ) );
              ])
        exp_max_size
    (* default size of two expression *)
  end

let rec from_be_to_hashcons (be : GKAT_2.bExp) : GKAT_Symb.BExp.t =
  match be with
  | Zero -> GKAT_Symb.BExp.zero
  | One -> GKAT_Symb.BExp.one
  | PBool str -> GKAT_Symb.BExp.pBool str
  | Or (b1, b2) ->
      GKAT_Symb.BExp.b_or (from_be_to_hashcons b1) (from_be_to_hashcons b2)
  | And (b1, b2) ->
      GKAT_Symb.BExp.b_and (from_be_to_hashcons b1) (from_be_to_hashcons b2)
  | Not b1 -> GKAT_Symb.BExp.b_not (from_be_to_hashcons b1)

let rec from_gkat_to_hashcon (exp1 : GKAT_2.gkat) : GKAT_Symb.Exp.t =
  match exp1 with
  | Pact p -> GKAT_Symb.Exp.p_act p
  | Seq (e, f) ->
      GKAT_Symb.Exp.seq (from_gkat_to_hashcon e) (from_gkat_to_hashcon f)
  | If (be, e, f) ->
      GKAT_Symb.Exp.if_then_else (from_be_to_hashcons be)
        (from_gkat_to_hashcon e) (from_gkat_to_hashcon f)
  | Test be -> GKAT_Symb.Exp.test (from_be_to_hashcons be)
  | While (be, e) ->
      GKAT_Symb.Exp.while_do (from_be_to_hashcons be) (from_gkat_to_hashcon e)

 (* let bench_rand_exp_symb =
  Test.make ~count:bench_count_ne
    ~name:"benchmarking symbolic algorithm with generated equivalence ne"
    (Gen.pair
       (GenExp.exp_sized bexp_max_size exp_max_size)
       (GenExp.exp_sized bexp_max_size exp_max_size))
    (fun (e1, e2) ->
      (*GKAT_Symb.BExp.(MLBDD.clear bdd);
      GKAT_Symb.BExp.(HashT.clear tbl);
      GKAT_Symb.Exp.(HashT.clear tbl);*)
      let ch, rand_fmt = mk_rand_fmt () in
      let e1_hashcons = from_gkat_to_hashcon e1 in
      let e2_hashcons = from_gkat_to_hashcon e2 in
      Fmt.pf rand_fmt "%a@.@." GKAT_Symb.Exp.pp e1_hashcons;
      Fmt.pf rand_fmt "%a@.@." GKAT_Symb.Exp.pp e2_hashcons;
      (* let start_time = Sys.time () in *)
      (* let result = GKAT_Symb.Derivatives.equiv e1_hashcons e2_hashcons in *)
      (* print_endline ("Result = " ^ string_of_bool result); *)
      Fmt.pf rand_fmt "(equiv 0)@.";
      close_out ch;
      true)
  *)

let bench_equiv_symb =
  Test.make ~count:bench_count_eq
    ~name:"benchmarking symbolic algorithm with generated equivalence eq"
    GenExp.gen_eq_exp (fun (e1, e2) ->
      (*GKAT_Symb.BExp.(MLBDD.clear bdd);
      GKAT_Symb.BExp.(HashT.clear tbl);
      GKAT_Symb.Exp.(HashT.clear tbl);*)
      let ch, equiv_fmt = mk_equiv_fmt () in
      let e1_hashcons = from_gkat_to_hashcon e1 in
      let e2_hashcons = from_gkat_to_hashcon e2 in
      Fmt.pf equiv_fmt "%a@.@." GKAT_Symb.Exp.pp e1_hashcons;
      Fmt.pf equiv_fmt "%a@.@." GKAT_Symb.Exp.pp e2_hashcons;
      (* let result = GKAT_Symb.Derivatives.equiv e1_hashcons e2_hashcons in *)
      (* print_endline ("Result = " ^ string_of_bool result); *)
      Fmt.pf equiv_fmt "(equiv 1)@.";
      close_out ch;
      true)

let _ =
  QCheck_runner.run_tests ~verbose:true [bench_equiv_symb]

(*
let _ = 
  QCheck_runner.run_tests ~verbose:true [bench_rand_exp_symb]
*)




