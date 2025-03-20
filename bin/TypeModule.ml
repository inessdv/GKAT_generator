

let rec pp_list pp fmt = function
  | [] -> ()
  | [ x ] -> pp fmt x
  | x :: xs -> Fmt.pf fmt "%a %a" pp x (pp_list pp) xs
module BExp = struct
  (** Module for working with boolean expressions *)
  type t = (t_ * Z3.Expr.expr) Hashcons.hash_consed
  (** The type for a hashconsed boolean expression *)

  (* The internal type of the boolean expression*)
  and t_ =
    | Zero
    | One
    | PBool of string * int
    | Or of t * t
    | And of t * t
    | Not of t

  module T_node = struct
    type t = t_ * Z3.Expr.expr

    let equal (t1, _) (t2, _) =
      match (t1, t2) with
      | Zero, Zero -> true
      | One, One -> true
      | PBool (_, i), PBool (_, j) -> i == j
      | Or (x1, y1), Or (x2, y2) -> x1 == x2 && y1 == y2
      | And (x1, y1), And (x2, y2) -> x1 == x2 && y1 == y2
      | Not x1, Not x2 -> x1 == x2
      | _ -> false

    let hash (t, _) =
      match t with
      | Zero -> Hashtbl.hash `Zero
      | One -> Hashtbl.hash `One
      | PBool (_, i) -> Hashtbl.hash (`PBool i)
      | Or (x, y) -> Hashtbl.hash (`Or (x.hkey, y.hkey))
      | And (x, y) -> Hashtbl.hash (`And (x.hkey, y.hkey))
      | Not x -> Hashtbl.hash (`Not x.hkey)
  end

  module HashT = Hashcons.Make (T_node)
  module Z3Cache = Hashtbl.Make (T_node)
  module NameCache = Hashtbl.Make (String)

  let hcons = HashT.create 1024
  let cache = Z3Cache.create 1024
  let name_cache = NameCache.create 1024
  let z3ctx = Z3.mk_context []
  let sat = Z3.Tactic.(mk_tactic z3ctx "sat")
  let hashcons = HashT.hashcons hcons
  let zero : t = hashcons @@ (Zero, Z3.Boolean.mk_false z3ctx)
  let one : t = hashcons @@ (One, Z3.Boolean.mk_true z3ctx)

  let reset () =
    Z3.Memory.reset ();
    Z3Cache.clear cache;
    NameCache.clear name_cache;
    HashT.clear hcons

  let pBool (str : string) : t =
    let x =
      match NameCache.find_opt name_cache str with
      | Some x -> x
      | None ->
          let x = Z3.Boolean.mk_const_s z3ctx str in
          NameCache.add name_cache str x;
          x
    in
    hashcons @@ (PBool (str, Hashtbl.hash str), x)

  let b_not (b1 : t) : t =
    if b1 == one then zero
    else if b1 == zero then one
    else
      let _, b1_ = b1.node in
      hashcons @@ (Not b1, Z3.Boolean.mk_not z3ctx b1_)

  let b_or (b1 : t) (b2 : t) : t =
    if b1 == one then one
    else if b2 == one then one
    else if b1 == zero then b2
    else if b2 == zero then b1
    else if b1 == b2 then b1
    else if b1 == b_not b2 then one
    else
      let _, b1_ = b1.node in
      let _, b2_ = b2.node in
      hashcons @@ (Or (b1, b2), Z3.Boolean.mk_or z3ctx [ b1_; b2_ ])

  let b_and (b1 : t) (b2 : t) : t =
    if b1 == one then b2
    else if b2 == one then b1
    else if b1 == zero then zero
    else if b2 == zero then zero
    else if b1 == b2 then b1
    else if b1 == b_not b2 then zero
    else
      let _, b1_ = b1.node in
      let _, b2_ = b2.node in
      hashcons @@ (And (b1, b2), Z3.Boolean.mk_and z3ctx [ b1_; b2_ ])

  (** convert a boolean expression to z3 expression *)
  let to_z3 (b : t) : Z3.Expr.expr = snd b.node

  let solver = Z3.Solver.mk_solver z3ctx None
  let equiv_count = ref 0
  let is_false_count = ref 0
  let is_false_cached = ref 0
  let is_false_time = ref 0.
  let equiv_time = ref 0.

  let is_false (bexp : t) : bool =
    let open Z3 in
    incr is_false_count;
    let start_time = Sys.time () in
    let b =
      match Z3Cache.find_opt cache bexp.node with
      | Some b ->
          incr is_false_cached;
          b
      | None ->
          let goal = Goal.mk_goal z3ctx false false false in
          Goal.add goal [ to_z3 bexp ];
          let ar = Tactic.apply sat goal None in
          let b =
            Goal.(is_decided_unsat (Tactic.ApplyResult.get_subgoal ar 0))
          in
          Z3Cache.add cache bexp.node b;
          b
    in
    is_false_time := !is_false_time +. (Sys.time () -. start_time);
    b

  (** Test if two boolean expressions is semantically equivelant. *)
  let equiv b1 b2 =
    let open Z3 in
    incr equiv_count;
    let start_time = Sys.time () in
    let b =
      let b1 = to_z3 b1 in
      let b2 = to_z3 b2 in
      let goal = Goal.mk_goal z3ctx false false false in
      Goal.add goal [ Z3.Boolean.(mk_not z3ctx (mk_iff z3ctx b1 b2)) ];
      let ar = Tactic.apply sat goal None in
      Goal.(is_decided_unsat (Tactic.ApplyResult.get_subgoal ar 0))
    in
    equiv_time := !equiv_time +. (Sys.time () -. start_time);
    b

  let pprint e = Z3.Expr.to_string @@ to_z3 e

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
    | Zero -> Fmt.pf fmt "0"
    | One -> Fmt.pf fmt "1"
    | PBool (s, _) -> Fmt.pf fmt "%s" s
    | Or _ ->
        let bexps = gather_or bexp in
        Fmt.pf fmt "@[(or@;<1 2>@[%a@])@]" (pp_list pp) bexps
    | And _ ->
        let bexps = gather_and bexp in
        Fmt.pf fmt "@[(and@;<1 2>@[%a@])@]" (Fmt.list ~sep:Fmt.sp pp) bexps
    | Not b -> Fmt.pf fmt "@[(not@;<1 2>@[%a@])@]" pp b
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

  let hcons = HashT.create 1024
  let hashcons : t_ -> t = HashT.hashcons hcons
  let p_act (p : string) : t = hashcons @@ Pact (p, Hashtbl.hash p)
  let test (b : BExp.t) : t = hashcons @@ Test b
  let skip : t = test BExp.one
  let fail : t = test BExp.zero
  let reset () = HashT.clear hcons

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

  let pprint (exp : t) =
    let rec helper (exp : t) : string * int =
      match exp.node with
      | Pact (p, _) -> (p, 0)
      | Seq (e1, e2) ->
          let s1, p1 = helper e1 in
          let s2, p2 = helper e2 in
          let s1' = if p1 < 2 then s1 else "(" ^ s1 ^ ")" in
          let s2' = if p2 < 2 then s2 else "(" ^ s2 ^ ")" in
          (s1' ^ " ; " ^ s2', 2)
      | If (b, e1, e2) ->
          let bs = BExp.pprint b in
          let s1, p1 = helper e1 in
          let s2, p2 = helper e2 in
          let s1' = if p1 <= 3 then s1 else "(" ^ s1 ^ ")" in
          let s2' = if p2 < 3 then s2 else "(" ^ s2 ^ ")" in
          ("if " ^ bs ^ " then " ^ s1' ^ " else " ^ s2', 3)
      | Test b ->
          let bs = BExp.pprint b in
          (bs, 1)
      | While (b, e) ->
          let bs = BExp.pprint b in
          let s, p = helper e in
          let s' = if p <= 1 then s else "(" ^ s ^ ")" in
          ("while " ^ bs ^ " do " ^ s' ^ " done", 1)
    in
    fst @@ helper exp

    let rec pp fmt (exp : t) =
      let rec gather_seq (exp : t) =
        match exp.node with Seq (e1, e2) -> e1 :: gather_seq e2 | _ -> [ exp ]
      in
      match exp.node with
      | Pact (p, _) -> Fmt.pf fmt "%s" p
      | Seq _ ->
          let exps = gather_seq exp in
          Fmt.pf fmt "@[(seq@;<1 2>@[%a@])@]" (Fmt.list ~sep:Fmt.sp pp) exps
      | If (b, e1, e2) ->
        Fmt.pf fmt "@[(if@;<1 2>@[%a@]@;<1 2>@[%a@]@;<1 2>@[%a@])@]" BExp.pp b pp e1
            pp e2
      | Test b -> Fmt.pf fmt "@[(test@;<1 2>@[%a@])@]" BExp.pp b
      | While (b, e) ->
        Fmt.pf fmt "@[(while@;<1 2>@[%a@]@;<1 2>@[%a@])@]" BExp.pp b pp e
end
type bExp =
  | Zero
  | One
  | PBool of string
  | Or of bExp * bExp
  | And of bExp * bExp
  | Not of bExp

type gkat =
  | Pact of string
  | Seq of gkat * gkat
  | If of bExp * gkat * gkat
  | Test of bExp
  | While of bExp * gkat

let p_act (p : string) :gkat= Pact p
let test (b : bExp) : gkat = Test b
let skip : gkat = test One
let fail : gkat = test Zero
