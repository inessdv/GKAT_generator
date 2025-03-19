open KAT_Set
open KAT_Set.Print

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

  let rec from_BE_to_KAT (exp : bExp) : kat =
    match exp with
    | Zero -> Zero
    | One -> One
    | PBool b -> PBool b
    | Or (b1, b2) -> Union (from_BE_to_KAT b1, from_BE_to_KAT b2)
    | And (b1, b2) -> Conc (from_BE_to_KAT b1, from_BE_to_KAT b2)
    | Not b -> (Not (from_BE_to_KAT b))
  
  let rec from_GKAT_to_KAT (exp : gkat) : kat =
    match exp with
    | Pact p -> PAct p
    | Seq (e1, e2) -> Conc (from_GKAT_to_KAT e1, from_GKAT_to_KAT e2)
    | If (b, e1, e2) ->
        Union
          ( Conc (from_BE_to_KAT b, from_GKAT_to_KAT e1),
            Conc (Not (from_BE_to_KAT b), from_GKAT_to_KAT e2) )
    | Test b -> from_BE_to_KAT b
    | While (b, e) ->
        Conc
          ( Star (Conc (from_BE_to_KAT b, from_GKAT_to_KAT e)),
            Not (from_BE_to_KAT b) )


  module Print1 = struct
    let gpprint (exp : gkat): string =
      let kat_exp = from_GKAT_to_KAT exp in
        pprint kat_exp
  
  end
  
  module Print2 = struct
  
    (*Printer helper function for bexp expressions*)
    let rec pprint_bexp_with_p (bexp : bExp) =
      match bexp with
      | Zero -> ("0", 0)
      | One -> ("1", 0)
      | PBool b -> (b, 0)
      | Or (b1, b2) ->
        let str1, prec1 = pprint_bexp_with_p b1 in
        let str2, prec2 = pprint_bexp_with_p b2 in
        let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
        let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
        (str1' ^ " or " ^ str2', 3)
      | And (b1, b2) ->
        let str1, prec1 = pprint_bexp_with_p b1 in
        let str2, prec2 = pprint_bexp_with_p b2 in
        let str1' = if prec1 > 2 then "(" ^ str1 ^ ")" else str1 in
        let str2' = if prec2 > 2 then "(" ^ str2 ^ ")" else str2 in
        (str1' ^ " and " ^ str2', 3)
      | Not b ->
        let str, prec = pprint_bexp_with_p b in
  
        if prec > 0 then ("~(" ^ str ^ ")", 1) else ("~" ^ str, 1)
      
      (* Print bexp without precedence number *)
      let pprint_bexp (bexp : bExp) =
      let str, _ = pprint_bexp_with_p bexp in
      str
  
        (*pretty printer for gkat*)
    let pprint (exp : gkat) =
      let rec helper (exp : gkat) : string * int =
        match exp with
        | Pact p -> (p, 0)
        | Seq (e1, e2) ->
          let s1, p1 = helper e1 in
          let s2, p2 = helper e2 in
          let s1' = if p1 < 2 then s1 else "(" ^ s1 ^ ")" in
          let s2' = if p2 < 2 then s2 else "(" ^ s2 ^ ")" in
          (s1' ^ " * " ^ s2', 2)
        | If (b, e1, e2) ->
          let bs, _ = pprint_bexp_with_p b in
          let s1, p1 = helper e1 in
          let s2, p2 = helper e2 in
          let s1' = if p1 <= 3 then s1 else "(" ^ s1 ^ ")" in
          let s2' = if p2 < 3 then s2 else "(" ^ s2 ^ ")" in
          ("if " ^ bs ^ " then " ^ s1' ^ " else " ^ s2', 3)
        | Test b ->
          let bs, _ = pprint_bexp_with_p b in
          (bs, 1)
        | While (b, e) ->
          let bs, _ = pprint_bexp_with_p b in
          let s, p = helper e in
          let s' = if p <= 1 then s else "(" ^ s ^ ")" in
          ("while " ^ bs ^ " do " ^ s' ^ " done", 1)
      in
  
      let str, _ = helper exp in
      str
  end

  (* let seq (e : gkat) (f : gkat) : gkat =
    match (e, f) with
    | Test a, Test b -> test (BExp.b_and a b)
    | _ ->
        if e == skip then f
        else if f == skip then e
        else if e == fail then fail
        else if f == fail then fail
        else Seq (e, f)

  let if_then_else (b : bExp.t) (e : t) (f : t) : t =
    if b == BExp.one then e
    else if b == BExp.zero then f
    else if e == fail then seq (test @@ BExp.b_not b) f
    else if f == fail then seq (test b) f
    else hashcons @@ If (b, e, f)

  let while_do (b : BExp.t) (e : t) : t = hashcons @@ While (b, e) *)

(**simplifying kat function*)
let rec simplify_kat (e:kat): kat =
  match e with
  | Zero -> Zero
  | One -> One
  | PAct _ -> e
  | PBool _ -> e
  | Union (e1,Zero) -> simplify_kat e1
  | Union (Zero,e2) -> simplify_kat e2
  | Union (e1,e2) -> Union (simplify_kat e1,simplify_kat e2)
  | Conc (_,Zero)-> Zero
  | Conc (Zero,_)-> Zero
  | Conc (e1,One)-> simplify_kat e1
  | Conc (One,e2)-> simplify_kat e2
  | Conc (e1,e2)-> Conc (simplify_kat e1,simplify_kat e2)
  | Star e -> Star (simplify_kat e)
  | Not One -> Zero
  | Not Zero -> One
  | Not (Not e1) -> simplify_kat e1
  | Not e1 -> Not (simplify_kat e1)

let gKat_equiv (exp1 : gkat) (exp2 : gkat) : bool =
  print_string ("exp1: " ^ Print2.pprint exp1);
  print_newline ();
  print_string ("exp2: " ^ Print2.pprint exp2);
  print_newline ();
  let e1 = simplify_kat (from_GKAT_to_KAT exp1) in
  let e2 = simplify_kat (from_GKAT_to_KAT exp2) in
  print_string ("ekat1: " ^ Print.pprint e1);
  print_newline ();
  print_string ("ekat2: " ^ Print.pprint e2);
  print_newline ();
  print_endline (string_of_bool (equiv e1 e2));
  equiv e1 e2


(* Expression 1: if 0 or b1 then b2 else while b2 do b2 done *)
let example1 = If (
  Or(Zero, PBool("b1")),   (* 0 or b1 *)
  Pact("b2"),              (* then b2 *)
  While(                   (* else *)
    PBool("b2"),           (* while b2 *)
    Pact("b1")             (* do b1 *)
  )
)

(* Expression 2: if ~b1 then while b2 and 1 do b1 done else b2 *)
let example2 = If (
  Not (PBool("b1")),       (* not b1 *)
  While (And (PBool("b2"),One), Pact("b1")), (* then while b2 and 1 do b1*)
  Pact("b2")             
  )

(* 1 *)
let exp1 = from_BE_to_KAT One
(* b1 + 1 *)
let exp2 = from_BE_to_KAT (Or (PBool("b1"),One))


let test1 =   While(                   
PBool("b2"),           
((Seq (Test(PBool("b1")), Pact("b1")))))

let test2 = 
  While (
    PBool("b2"), 
    Test(PBool("b1"))
  )

let e1 = 
  While (
    Or(PBool("b1"),PBool("b1")), 
    While((And(PBool("b1"),PBool("b2"))),Pact("p0"))
  )

let e2 = 
  While(
    PBool("b1"), 
    Test(PBool("b1"))
)

