open Fmt

let rec pp_list pp fmt = function
  | [] -> ()
  | [ x ] -> pp fmt x
  | x :: xs -> pf fmt "%a %a" pp x (pp_list pp) xs

module BExp = struct
  (** Module for working with boolean expressions *)
  type t = (t_ * bool option ref) Hashcons.hash_consed
  (** The type for a hashconsed boolean expression *)

  (* The internal type of the boolean expression*)
  and t_ =
    | Zero
    | One
    | PBool of string * int
    | Or of t * t
    | And of t * t
    | Not of t

  let t_equal t1 t2 =
    match (t1, t2) with
    | Zero, Zero -> true
    | One, One -> true
    | PBool (_, i), PBool (_, j) -> i == j
    | Or (x1, y1), Or (x2, y2) -> x1 == x2 && y1 == y2
    | And (x1, y1), And (x2, y2) -> x1 == x2 && y1 == y2
    | Not x1, Not x2 -> x1 == x2
    | _ -> false

  let t_hash t =
    match t with
    | Zero -> Hashtbl.hash `Zero
    | One -> Hashtbl.hash `One
    | PBool (_, i) -> Hashtbl.hash (`PBool i)
    | Or (x, y) -> Hashtbl.hash (`Or (x.hkey, y.hkey))
    | And (x, y) -> Hashtbl.hash (`And (x.hkey, y.hkey))
    | Not x -> Hashtbl.hash (`Not x.hkey)

  module T_node = struct
    type t = t_ * bool option ref

    let equal (t1, _) (t2, _) = t_equal t1 t2
    let hash (t, _) = t_hash t
  end

  module HashT = Hashcons.Make (T_node)

  let tbl = HashT.create 4096
  let bdd = MLBDD.init ~cache:(4096 * 4096) ()

  (* let cache = Cache.create (4096 * 4096) *)
  let hashcons = HashT.hashcons tbl
  let zero : t = hashcons @@ (Zero, ref (Some true))
  let one : t = hashcons @@ (One, ref (Some false))

  let reset () =
    HashT.clear tbl;
    MLBDD.clear bdd
  (* Cache.clear cache *)

  let pBool (str : string) : t =
    let h = Hashtbl.hash str in
    hashcons @@ (PBool (str, h), ref None)

  let b_not (b1 : t) : t =
    if b1 == one then zero
    else if b1 == zero then one
    else
      let _, r1 = b1.node in
      let opt = match !r1 with Some true -> Some false | _ -> None in
      hashcons @@ (Not b1, ref opt)

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else
      let _, r1 = b1.node in
      let _, r2 = b2.node in
      let r =
        match (!r1, !r2) with
        | Some true, _ -> r2
        | _, Some true -> r1
        | _ -> ref None
      in
      hashcons @@ (Or (b1, b2), r)

  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else
      let _, r1 = b1.node in
      let _, r2 = b2.node in
      let r =
        match (!r1, !r2) with
        | Some true, _ -> ref (Some true)
        | _, Some true -> ref (Some true)
        | _ -> ref None
      in
      hashcons @@ (And (b1, b2), r)

  (** convert a boolean expression to z3 expression *)
  let rec to_bdd (b : t) : MLBDD.t =
    let open MLBDD in
    match fst b.node with
    | Zero -> dfalse bdd
    | One -> dtrue bdd
    | PBool (_, i) -> ithvar bdd i
    | Or (b1, b2) -> dor (to_bdd b1) (to_bdd b2)
    | And (b1, b2) -> dand (to_bdd b1) (to_bdd b2)
    | Not b -> dnot (to_bdd b)

  let equiv_count = ref 0
  let is_false_count = ref 0
  let is_false_cached = ref 0
  let is_false_time = ref 0.
  let equiv_time = ref 0.

  let is_false (bexp : t) : bool =
    incr is_false_count;
    let start_time = Sys.time () in
    let _, r = bexp.node in
    let b =
      match !r with
      | Some b ->
          incr is_false_cached;
          b
      | None ->
          let b = MLBDD.is_false (to_bdd bexp) in
          r := Some b;
          b
    in
    is_false_time := !is_false_time +. (Sys.time () -. start_time);
    b

  (** Test if two boolean expressions is semantically equivelant. *)
  let equiv (b1 : t) (b2 : t) : bool =
    incr equiv_count;
    let start_time = Sys.time () in
    let b = MLBDD.equal (to_bdd b1) (to_bdd b2) in
    equiv_time := !equiv_time +. (Sys.time () -. start_time);
    b

  let rec pp fmt (bexp : t) =
    let rec gather_or (bexp : t) =
      match fst bexp.node with
      | Or (b1, b2) -> b1 :: gather_or b2
      | _ -> [ bexp ]
    in
    let rec gather_and (bexp : t) =
      match fst bexp.node with
      | And (b1, b2) -> b1 :: gather_and b2
      | _ -> [ bexp ]
    in
    match fst bexp.node with
    | Zero -> pf fmt "0"
    | One -> pf fmt "1"
    | PBool (s, _) -> pf fmt "%s" s
    | Or _ ->
        let bexps = gather_or bexp in
        pf fmt "@[(or@;<1 2>@[%a@])@]" (pp_list pp) bexps
    | And _ ->
        let bexps = gather_and bexp in
        pf fmt "@[(and@;<1 2>@[%a@])@]" (list ~sep:sp pp) bexps
    | Not b -> pf fmt "@[(not@;<1 2>@[%a@])@]" pp b
end

module Exp = struct
  type t = t_ Hashcons.hash_consed
  (** hashconsed GKAT expression*)

  and t_ =
    | Pact of string * int
    | Seq of t * t
    | If of BExp.t * t * t
    | Test of BExp.t
    | While of BExp.t * t

  module T_node = struct
    type t = t_

    let equal t1 t2 =
      match (t1, t2) with
      | Pact (_, i), Pact (_, j) -> i == j
      | Seq (x1, y1), Seq (x2, y2) -> x1 == x2 && y1 == y2
      | If (b1, x1, y1), If (b2, x2, y2) -> b1 == b2 && x1 == x2 && y1 == y2
      | Test b1, Test b2 -> b1 == b2
      | While (b1, t1), While (b2, t2) -> b1 == b2 && t1 == t2
      | _ -> false

    let hash t =
      match t with
      | Pact (_, i) -> Hashtbl.hash (`Pact i)
      | Seq (x, y) -> Hashtbl.hash (`Seq (x.hkey, y.hkey))
      | If (b, x, y) -> Hashtbl.hash (`If (b.hkey, x.hkey, y.hkey))
      | Test b -> Hashtbl.hash (`Text b.hkey)
      | While (b, x) -> Hashtbl.hash (`While (b.hkey, x.hkey))
  end

  module HashT = Hashcons.Make (T_node)

  (** table used for hash consing 
  notice because of hash consing, we can build *)
  let tbl = HashT.create 4096

  let hashcons : t_ -> t = HashT.hashcons tbl
  let p_act (p : string) : t = hashcons @@ Pact (p, Hashtbl.hash p)
  let test (b : BExp.t) : t = hashcons @@ Test b
  let skip : t = test BExp.one
  let fail : t = test BExp.zero
  let reset () = HashT.clear tbl

  let seq (e : t) (f : t) : t =
    match (e.node, f.node) with
    | Test a, Test b -> test (BExp.b_and a b)
    | _ ->
        if e == skip then f
        else if f == skip then e
        else if e == fail then fail
        else if f == fail then fail
        else hashcons @@ Seq (e, f)

  let if_then_else (b : BExp.t) (e : t) (f : t) : t =
    if b == BExp.one then e
    else if b == BExp.zero then f
    else if e == fail then seq (test @@ BExp.b_not b) f
    else if f == fail then seq (test b) e
    else hashcons @@ If (b, e, f)

  let while_do (b : BExp.t) (e : t) : t = hashcons @@ While (b, e)
  (* if b == BExp.zero then skip
     else if b == BExp.one then fail
     else if e == skip || e == fail then test @@ BExp.b_not b
     else *)

  (** Return the number of primitive actions in the expression*)
  let rec num_pact (e : t) =
    match e.node with
    | Pact _ -> 1
    | Seq (e1, e2) -> num_pact e1 + num_pact e2
    | If (_, e1, e2) -> num_pact e1 + num_pact e2
    | Test _ -> 0
    | While (_, e1) -> num_pact e1

  (** Return the number of test expression in the expression*)
  let rec num_bexp (e : t) =
    match e.node with
    | Pact _ -> 0
    | Seq (e1, e2) -> num_bexp e1 + num_bexp e2
    | If (_, e1, e2) -> 1 + num_bexp e1 + num_bexp e2
    | Test _ -> 1
    | While (_, e1) -> 1 + num_bexp e1

  (** number of sequencing operation in the input expression *)
  let rec num_seq (e : t) =
    match e.node with
    | Pact _ -> 0
    | Seq (e1, e2) -> 1 + num_seq e1 + num_seq e2
    | If (_, e1, e2) -> num_seq e1 + num_seq e2
    | Test _ -> 0
    | While (_, e1) -> num_seq e1

  (** number of if statements in the input expression *)
  let rec num_if (e : t) =
    match e.node with
    | Pact _ -> 0
    | Seq (e1, e2) -> num_if e1 + num_if e2
    | If (_, e1, e2) -> 1 + num_if e1 + num_if e2
    | Test _ -> 0
    | While (_, e1) -> num_if e1

  (** number of while loop in the input expression *)
  let rec num_while (e : t) =
    match e.node with
    | Pact _ -> 0
    | Seq (e1, e2) -> num_while e1 + num_while e2
    | If (_, e1, e2) -> num_while e1 + num_while e2
    | Test _ -> 0
    | While (_, e1) -> 1 + num_while e1

  let rec pp fmt (exp : t) =
    let rec gather_seq (exp : t) =
      match exp.node with Seq (e1, e2) -> e1 :: gather_seq e2 | _ -> [ exp ]
    in
    match exp.node with
    | Pact (p, _) -> pf fmt "%s" p
    | Seq _ ->
        let exps = gather_seq exp in
        pf fmt "@[(seq@;<1 2>@[%a@])@]" (list ~sep:sp pp) exps
    | If (b, e1, e2) ->
        pf fmt "@[(if@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@])@]" BExp.pp b pp e1
          pp e2
    | Test b -> pf fmt "@[(test@;<1 2>@[%a@])@]" BExp.pp b
    | While (b, e) ->
        pf fmt "@[(while@;<1 2>@[%a@]@;<1 2>@[%a@])@]" BExp.pp b pp e
end

module Derivatives = struct
  (** defines derivatives *)

  module Hmap = Hashcons.Hmap

  module HSet = Hashcons.Hset
  (** a fast immutable map for hashconsed key *)

  (** The epsilon of the expression,
  The boolean expression consists of all the atoms 
  that is accepted by the expression *)

  module ExpTbl = Hashtbl.Make (struct
    type t = Exp.t

    let hash (e : t) = e.hkey
    let equal e1 e2 = e1 == e2
  end)

  module ExpHSet = struct
    type t = unit ExpTbl.t

    let create : int -> t = ExpTbl.create
    let add (exp : Exp.t) (s : t) : unit = ExpTbl.add s exp ()
    let remove (exp : Exp.t) (s : t) : unit = ExpTbl.remove s exp

    let mem (exp : Exp.t) (s : t) : bool =
      Option.is_some @@ ExpTbl.find_opt s exp

    let add_to_fst (hset1 : t) (hset2 : Exp.t list) : unit =
      List.iter (fun exp -> add exp hset1) hset2

    let clear = ExpTbl.clear
    let length = ExpTbl.length
  end

  let rec epsilon (exp : Exp.t) : BExp.t =
    match exp.node with
    | Pact _ -> BExp.zero
    | Seq (e, f) -> BExp.b_and (epsilon e) (epsilon f)
    | If (be, e, f) ->
        BExp.b_or
          (BExp.b_and be (epsilon e))
          (BExp.b_and (BExp.b_not be) (epsilon f))
    | Test be -> be
    | While (be, _) -> BExp.b_not be

  (** The derivative of a expression: δ ∈ exp -> (BExp ↛ exp × Σ)
  This uses the map representation of the derivative for the ease of implementation,
  and primitive action is encoded as a string *)

  let combine_BE_with_a (be : BExp.t) (m : (BExp.t * (Exp.t * int)) list) :
      (BExp.t * (Exp.t * int)) list =
    List.map (fun (a, b) -> (BExp.b_and a be, b)) m

  let while_helper (be : BExp.t) (exp : Exp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map
      (fun (a, (e', p)) ->
        (BExp.b_and a be, (Exp.seq e' (Exp.while_do be exp), p)))
      m

  let sequence_helper_without_epsilon (exp2 : Exp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map (fun (b, (e', p)) -> (b, (Exp.seq e' exp2, p))) m

  let sequence_helper_with_epsilon (eps : BExp.t)
      (m : (BExp.t * (Exp.t * int)) list) : (BExp.t * (Exp.t * int)) list =
    List.map (fun (b, pair) -> (BExp.b_and b eps, pair)) m

  let rec derivative (exp : Exp.t) : (BExp.t * (Exp.t * int)) list =
    match exp.node with
    | Test _ -> []
    | Pact (_, p) -> [ (BExp.one, (Exp.test BExp.one, p)) ]
    | If (be, exp1, exp2) ->
        (* get rid of repetitions--> do List.sort_uniq**)
        combine_BE_with_a be (derivative exp1)
        @ combine_BE_with_a (BExp.b_not be) (derivative exp2)
    | Seq (e, f) ->
        let eps_of_e = epsilon e in
        let derivative_of_exp1 = derivative e in
        let derivative_of_exp2 = derivative f in
        sequence_helper_without_epsilon f derivative_of_exp1
        @ sequence_helper_with_epsilon eps_of_e derivative_of_exp2
    | While (be, e) ->
        let derive_e = derivative e in
        while_helper be e derive_e

  module DeadExps : sig
    val is_dead : Exp.t -> bool
    val known_dead : Exp.t -> bool
    val clear_dead : unit
    val length : int
  end = struct
    (** The module to encapsolate the logic to check dead*)

    (** states (expressions) that are known to be dead
  
    its size 251 is a magic number, as a place holder*)
    let dead_states : ExpHSet.t = ExpHSet.create 251

    (** Detect whether an expression is *known* to be dead.
    
    A fast alternative to `is_dead`, 
    when it returns `false`, the expression is not necessarily live.*)
    let known_dead exp = ExpHSet.mem exp dead_states

    let clear_dead = ExpHSet.clear dead_states
    let length = ExpHSet.length dead_states

    type visitRes =
      | KnownDead
          (** the visited expression is *known* to be dead, i.e. in `dead_states`*)
      | Live
          (** the visited node is live, i.e. accepting state is found in the visit *)
      | Unknown of Exp.t_ HSet.t
          (** the visited node is unknown to be dead or live, 
          the arugument is all the explored expressions while visiting that node*)

    (** helper to `visit`, visit all the decedents of an expression, return a visit result
  
    - return `Live` if any of them is returning live, 
    - return `Dead` if all of them are returning dead, 
    - return `Unknown` otherwise *)
    let rec visit_decedents (explored : Exp.t_ HSet.t) (exps : Exp.t list) :
        visitRes =
      match exps with
      | [] -> Unknown explored
      | x1 :: xs -> (
          match visit explored x1 with
          | Live -> Live
          | KnownDead -> visit_decedents (HSet.add x1 explored) xs
          | Unknown states -> visit_decedents (HSet.union explored states) xs)

    (** visit a single expression, *)
    and visit (explored : Exp.t_ HSet.t) (exp : Exp.t) : visitRes =
      (* print_endline ("visiting "^Exp.pprint exp); *)
      if known_dead exp then KnownDead
      else if HSet.mem exp explored then Unknown explored
      else
        (* explore the current *)
        let explored = HSet.add exp explored in
        if BExp.is_false @@ epsilon exp then
          (* expression is not accepting*)
          let deriv = derivative exp in
          (* computing the next step, notice we need to filter out the unreachable expression,
             where the symbolic derivative `b_exp` is false *)
          let next_exps =
            List.filter_map
              (fun (b_exp, (exp, _)) ->
                if BExp.is_false b_exp then None else Some exp)
              deriv
          in
          visit_decedents explored next_exps
        else (* expression is accepting*)
          Live

    (** Check whether an expression is dead.
    
    When it returns false, the expression is necessarily live.*)
    let is_dead (exp : Exp.t) : bool =
      (* print_endline ("checking whether exp "^Exp.pprint exp^" is dead");  *)
      match visit HSet.empty exp with
      (* if it is unknown wether it is dead
         after exploring all of its reachable state,
         then it cannot reach any accepting states,
         hence the state `s` is dead*)
      | Unknown s ->
          (* print_endline ("final result, unknown, hence dead"); *)
          let exp_list = HSet.elements s in
          ExpHSet.add_to_fst dead_states exp_list;
          true
      | Live ->
          (* print_endline "final result, live";  *)
          false
      | KnownDead ->
          (* print_endline "final result, known dead";  *)
          true
  end

  (** A table that maps the the expression to its union find element *)
  let union_find_tbl = ExpTbl.create 251

  (** Add expression to hash table if it has not yet been added **)
  let exp_ele (exp : Exp.t) : Exp.t UnionFind.elem =
    match ExpTbl.find_opt union_find_tbl exp with
    | Some exp_ele -> exp_ele
    | None ->
        let exp_ele = UnionFind.make exp in
        ExpTbl.add union_find_tbl exp exp_ele;
        exp_ele

  let print_tuple tup =
    let s, i = tup in
    Printf.printf "(%s, %d)\n" s i

  (** get the reject expression 
  
  logically, the expression can be written as follows: 
  ¬ ϵ(e) ∧ ¬ (⋁_{ψ ↦ (e', p) ∈ δ(e)} ψ) *)
  let reject (exp : Exp.t) : BExp.t =
    let exp_derivatives = derivative exp in
    let epsilon = epsilon exp in
    let transitions =
      List.fold_left
        (fun acc (be, (_, _)) -> BExp.b_or acc be)
        BExp.zero exp_derivatives
    in
    (*print_endline ("Checking reject for ");
      print_string (Print2.pprint (dehashcons_gkat exp));
      print_newline ();
      print_tuple (Print2.pprint_bexp (dehashcons_bexp epsilon));
      print_newline ();*)
    let result = BExp.b_and (BExp.b_not epsilon) (BExp.b_not transitions) in
    (*let result_dehash = dehashcons_bexp result in
      print_tuple (Print2.pprint_bexp  result_dehash);*)
    result

  let rec equiv_helper (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let reject1 = reject exp1 in
    let reject2 = reject exp2 in

    (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
       print_endline ( "Exp 2: " ^Exp.pprint exp2); *)
    let exp1_ele = exp_ele exp1 in
    let exp2_ele = exp_ele exp2 in

    (* Check if the expressions have already been marked as equiv **)
    if UnionFind.eq exp1_ele exp2_ele then true
    else if
      (* if both are dead, then they are equivalent **)
      DeadExps.known_dead exp1
    then (* print_endline ("exp1 is dead"); *)
      DeadExps.is_dead exp2
    else if DeadExps.known_dead exp2 then
      (* print_endline ("exp2 is dead");
         print_endline ("is exp1 dead?" ^ string_of_bool @@ DeadExps.is_dead exp1); *)
      DeadExps.is_dead exp1
    else
      (*  Logical connection here instead of if **)
      let epsilon_assert = BExp.equiv (epsilon exp1) (epsilon exp2) in
      (* print_endline ("Checking same espilon: ");
         print_endline (string_of_bool epsilon_assert); *)
      epsilon_assert
      &&
      let f_derivatives = derivative exp2 in
      let e_derivatives = derivative exp1 in

      (let assert1 =
         List.for_all
           (fun (be, (exp, _)) ->
             BExp.is_false (BExp.b_and reject1 be) || DeadExps.is_dead exp)
           f_derivatives
       in
       (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
          print_endline ( "Exp 2: " ^Exp.pprint exp2);
          print_endline ("assertion1 for: forall ψ_f ↦ (f', q) ∈ δ(f), ( ρ(e) ∧ ψ_f = 0 || is_dead(f')) ");
          print_endline (string_of_bool assert1); *)
       assert1)
      && (let assert2 =
            List.for_all
              (fun (be, (exp, _)) ->
                BExp.is_false (BExp.b_and reject2 be) || DeadExps.is_dead exp)
              e_derivatives
          in
          (* print_endline ( "Exp 1: " ^Exp.pprint exp1);
             print_endline ( "Exp 2: " ^Exp.pprint exp2);
             print_endline ("assertion2 for: forall ψ_e ↦ (e', q) ∈ δ(f), ( ρ(f) ∧ ψ_f = 0 || is_dead(e')) ");
             print_endline (string_of_bool assert2); *)
          assert2)
      &&
      let assert3 =
        List.for_all
          (fun (be1, (next_exp1, p)) ->
            List.for_all
              (fun (be2, (next_exp2, q)) ->
                BExp.is_false (BExp.b_and be1 be2)
                ||
                if p = q then (
                  ignore @@ UnionFind.union exp1_ele exp2_ele;
                  equiv_helper next_exp1 next_exp2)
                else DeadExps.is_dead next_exp1 && DeadExps.is_dead next_exp2)
              f_derivatives)
          e_derivatives
      in
      assert3

  let equiv (exp1 : Exp.t) (exp2 : Exp.t) : bool =
    let equiv = equiv_helper exp1 exp2 in
    ExpTbl.clear union_find_tbl;
    BExp.reset ();
    Exp.reset ();
    equiv
end
