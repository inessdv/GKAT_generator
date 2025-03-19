open Common

(*Defining necessary types and modules*)

type kat =
  | Zero
  | One
  | PAct of string
  | PBool of string
  | Union of kat * kat
  | Conc of kat * kat
  | Star of kat
  | Not of kat

module KATSet = Set.Make (struct
  type t = kat

  let compare = compare
end)

module AtPactMap = Map.Make (struct
  type t = Atom.t * string (*change to Atom.t*)

  (** lexical ordering, compare atoms first, then compare the primitive action.*)
  let compare (at1, p1) (at2, p2) =
    let at_comp = Atom.compare at1 at2 in
    if at_comp = 0 then String.compare p1 p2 else at_comp
end)

module AtomSet = Set.Make (Atom)
(** Set of atoms **)

type derMap = KATSet.t AtPactMap.t
(** The derivative map of a expression, which is a (StringSet (atoms), String(pact)) mapped to as set of KAT expressions*)

module StringMap = Map.Make (String)
(** A map from string*)

module DerMapSet = Set.Make (struct
  type t = derMap

  let compare = compare
end)

type atPact = Atom.t * string

module AtPactSet = Set.Make (struct
  type t = Atom.t * string

  let compare = compare
end)

module PDerivPairSet = Set.Make (struct
  (* set of pairs of partial derivitives*)
  type t = KATSet.t * KATSet.t

  let compare = compare
end)

module Print = struct
  let pprint (exp : kat) =
    (*helper method, takes a expression, output the string,
        and **the precedence of the outer most expression** *)
    let rec helper (exp : kat) : string * int =
      match exp with
      | One -> ("1", 0)
      | Zero -> ("0", 0)
      | PAct c -> (c, 0)
      | PBool c -> (c, 0)
      | Star r ->
          let str, precedence = helper r in
          if precedence <= 0 then (str ^ "*", 0) else ("(" ^ str ^ ")*", 0)
      | Not r ->
          let str, precedence = helper r in
          if precedence <= 1 then ("~" ^ str, 1) else ("~(" ^ str ^ ")", 1)
      | Conc (r1, r2) ->
          let str1, precedence1 = helper r1 in
          let str2, precedence2 = helper r2 in
          let str1' = if precedence1 <= 2 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 2 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ " " ^ str2', 2)
      | Union (r1, r2) ->
          let str1, precedence1 = helper r1 in
          let str2, precedence2 = helper r2 in
          let str1' = if precedence1 <= 3 then str1 else "(" ^ str1 ^ ")" in
          let str2' = if precedence2 < 3 then str2 else "(" ^ str2 ^ ")" in
          (str1' ^ " + " ^ str2', 3)
    in
    let str, _ = helper exp in
    str

  let pprint_atPact_sum (heads : AtPactSet.t) =
    let heads = AtPactSet.to_list heads in
    let string_list =
      List.map (fun (atom, p) -> "head " ^ Atom.pprint atom ^ p) heads
    in
    String.concat " " string_list

  let pprint_sum (expset : KATSet.t) : string =
    let exp_list = KATSet.to_list expset in
    (*I can do pipeline here*)
    let string_list = List.map pprint exp_list in
    String.concat " " string_list

  let pprint_pder (pair : PDerivPairSet.t) : string =
    let pair_list = PDerivPairSet.to_list pair in
    let string_list =
      List.map
        (fun (x, y) -> ("( " ^ pprint_sum x) ^ ", and " ^ pprint_sum y ^ ")")
        pair_list
    in
    String.concat " " string_list

  let pprint_atoms (atoms : Atom.t list) : string =
    List.map (fun atom -> Atom.pprint atom) atoms |> String.concat "\n"

  let pprint_der_map (der_map : derMap) : string =
    let der_list = AtPactMap.to_list der_map in
    let der_str_list =
      List.map
        (fun ((atom, pact), kat) ->
          Atom.pprint atom ^ ", " ^ pact ^ " -> " ^ pprint_sum kat)
        der_list
    in
    String.concat "\n" der_str_list

  let pprint_der_maps (der_maps : DerMapSet.t) : string =
    let list_of_der_maps = DerMapSet.to_list der_maps in
    let string_list = List.map (fun x -> pprint_der_map x) list_of_der_maps in
    String.concat " " string_list
end

type katI =
  kat * bool (*True when expression is boolean, false when expression is KAT*)

let pAct p = (PAct p, false)
let pBool b = (PBool b, true)
let one = (One, true)
let zero = (Zero, true)

let union (e1 : katI) (e2 : katI) : katI =
  match (e1, e2) with
  | (Zero, _), _ -> e2
  | _, (Zero, _) -> e1
  | (k1, true), (k2, true) -> (Union (k1, k2), true)
  | (k1, _), (k2, _) -> (Union (k1, k2), false)

let conc (e1 : katI) (e2 : katI) : katI =
  match (e1, e2) with
  | (Zero, _), _ -> (Zero, true)
  | _, (Zero, _) -> (Zero, true)
  | (One, _), _ -> e2
  | _, (One, _) -> e1
  | (k1, true), (k2, true) ->
      ( Conc (k1, k2),
        true (*if k1==One and k2==One then One,true  else Zero,true*) )
  | (k1, false), (k2, false) -> (Conc (k1, k2), false)
  (*TODO: please fix this, conc can concatnate two types of expression*)
  | (k1, _), (k2, _) -> (Conc (k1, k2), false)

let not_b ((exp, expIsBExp) : kat * bool) =
  if expIsBExp then
    match exp with
    | One -> (Zero, true)
    | Zero -> (One, true)
    | _ -> (Not exp, true)
  else
    raise
      (Invalid_argument
         ("negation applied to non-boolean expression: " ^ Print.pprint exp))

let star ((exp, expIsBExp) : kat * bool) =
  if expIsBExp == false then (Star exp, false) else (One, true)

module KATISet = Set.Make (struct
  type t = katI

  let compare = compare
end)

let rec pbools_of (exp : kat) : PBoolSet.t =
  match exp with
  | One -> PBoolSet.empty
  | Zero -> PBoolSet.empty
  | PAct _ -> PBoolSet.empty
  | PBool b -> PBoolSet.singleton b
  | Conc (e1, e2) -> PBoolSet.union (pbools_of e1) (pbools_of e2)
  | Union (e1, e2) -> PBoolSet.union (pbools_of e1) (pbools_of e2)
  | Star e -> pbools_of e
  | Not eb -> pbools_of eb

(** empty word for KAT expressions**)
let rec epsilon (atom : Atom.t) (exp : kat) : bool =
  match exp with
  | Zero -> false
  | One -> true
  | PAct _ -> false
  | PBool b -> Atom.mem b atom (*if b <= atom, then b must be in the atom *)
  | Union (a, b) -> epsilon atom a || epsilon atom b
  | Conc (a, b) -> epsilon atom a && epsilon atom b
  | Star _ -> true
  | Not a -> not (epsilon atom a)

(** empty word for KATset**)
let epsilon_sum (atom : Atom.t) (sum : KATSet.t) : bool =
  KATSet.exists (fun exp -> epsilon atom exp) sum

(** union two derivative map **)
let union_der_map (der1 : derMap) (der2 : derMap) : derMap =
  AtPactMap.union
    (* combine two KAT sets with union, when their hds are the same*)
      (fun _ s1 s2 -> Some (KATSet.union s1 s2))
    der1 der2

let conc_alg (e1 : kat) (e2 : kat) : kat =
  match (e1, e2) with
  | One, _ -> e2
  | _, One -> e1
  | Zero, _ -> Zero
  | _, Zero -> Zero
  | _, _ -> Conc (e1, e2)

let conc_der_map (der_map : derMap) (exp : kat) : derMap =
  AtPactMap.map
    (fun derivs ->
      (* when concatenating with 1, elimination of map of the 1,
          we could also eliminate 0, as we'd get an empty set!!!*)
      KATSet.map (fun deriv -> conc_alg deriv exp) derivs)
    der_map

(** get the derivative map of an expression with respect to a set of boolean primitives*)
let rec get_der_map (pbools : PBoolSet.t) (exp : kat) : derMap =
  let map = 
  match exp with
  | PBool _ -> AtPactMap.empty
  (* der_map(p) = {(at, p) -> {1} | at ∈ atoms} *)
  | PAct p ->
      let atoms = Atom.of_p_bools pbools in
      let der_map_list =
        List.map (fun at -> ((at, p), KATSet.singleton One)) atoms
      in
      AtPactMap.of_list der_map_list
  | Union (e1, e2) ->
      union_der_map (get_der_map pbools e1) (get_der_map pbools e2)
  | Conc (e1, e2) ->
      (* the der map where the head is taken from e1 *)
      let der_map_exec_e1 = conc_der_map (get_der_map pbools e1) e2 in
      (* the der map where the head is taken from e2, but e1 accepts *)
      let der_map_acc_e1 =
        AtPactMap.filter
          (fun (at, _) _ -> epsilon at e1)
          (get_der_map pbools e2)
      in
      union_der_map der_map_exec_e1 der_map_acc_e1
  | Star e -> conc_der_map (get_der_map pbools e) (Star e)
  | _ -> AtPactMap.empty
    in
    print_endline ("der_map for exp: " ^Print.pprint exp);
    print_endline ("pbools: " ^ PBoolSet.pprint pbools);
    print_endline ("der_map: " ^Print.pprint_der_map map); map

(** Get the derivative map for a set of KATs (sum), represented as a set of terms **)
let get_der_map_sum (primitives : PBoolSet.t) (sum : KATSet.t) : DerMapSet.t =
  let der_maps =
    KATSet.to_list sum
    |> List.map (fun x -> get_der_map primitives x)
    |> DerMapSet.of_list
  in
   print_endline
    ("sum of derivative maps for!:" ^ Print.pprint_sum sum ^ " =("
    ^ Print.pprint_der_maps der_maps ^ " )"); 
  der_maps

(**hd function gets the set of all heads αp mapped in the derivative maps of a KAT**)
let hd (r : derMap) : AtPactSet.t =
  AtPactSet.of_list (List.map fst (AtPactMap.to_list r))

(** Function deriv collects all the partial derivatives of 
      a KAT expression in respect to a αp, that were computed 
      by derivative function. **)
let deriv (atp : atPact) (der_map : derMap) : KATSet.t =
  let atom, pact = atp in
  print_endline
    ("to extract derivs with respect to: " ^ Atom.pprint atom ^ ", " ^ pact
   ^ ":( "
    ^ Print.pprint_der_map der_map
    ^ ")"); 
  match AtPactMap.find_opt atp der_map with
  (*If the p doesn't exists then return empty*)
  | None ->
       print_endline (Atom.pprint atom ^ ", " ^ pact ^ " not found");
      KATSet.empty
  (*Otherwise return the sum*)
  | Some der_sum ->
       print_endline (Atom.pprint atom ^ ", " ^ pact ^ " found"); 
      der_sum

let hd_sum (sum : DerMapSet.t) : AtPactSet.t =
  let sumLinear = DerMapSet.to_list sum in
  (* union each head of term in the sum*)
  List.fold_left AtPactSet.union AtPactSet.empty (List.map hd sumLinear)

let deriv_sum (atp : atPact) (sum_der_map : DerMapSet.t) : KATSet.t =
  DerMapSet.to_list sum_der_map
  (*Take the derivative of each element of the sum*)
  |> List.map (deriv atp)
  (*Union the results*)
  |> List.fold_left KATSet.union KATSet.empty

(** returns whether two some has the same epsilon *)
let eps_sum_eq (sum1 : KATSet.t) (sum2 : KATSet.t) (atoms : Atom.t list) :
    bool =
  List.for_all (fun at -> epsilon_sum at sum1 = epsilon_sum at sum2) atoms

let derivatives (primitives : PBoolSet.t) ((r1, r2) : KATSet.t * KATSet.t) :
    PDerivPairSet.t =
  let der_map1 = get_der_map_sum primitives r1 in
  let der_map2 = get_der_map_sum primitives r2 in
  let heads = AtPactSet.union (hd_sum der_map1) (hd_sum der_map2) in
  (* print_endline (Print.pprint_atPact_sum heads); *)
  AtPactSet.to_list heads
  |> List.map (fun p ->
         let deriv_sum1 = deriv_sum p der_map1 in
         let deriv_sum2 = deriv_sum p der_map2 in
         let atom, pact = p in
         print_endline ("current head " ^ Atom.pprint atom ^ pact);
         print_endline
           ("derivatives for : ex1:" ^ Print.pprint_sum r1 ^ " ("
           ^ Print.pprint_sum deriv_sum1
           ^ ") ex2: " ^ Print.pprint_sum r2 ^ " ("
           ^ Print.pprint_sum deriv_sum2
           ^ ")"); 
         (deriv_sum1, deriv_sum2))
  |> PDerivPairSet.of_list

(** Equivalence Function **)
let equiv (e1 : kat) (e2 : kat) : bool =
  let pb_e1 = pbools_of e1 in
  let pb_e2 = pbools_of e2 in
   print_endline ("pbools of e1: " ^ Print.pprint e1 ^ ": "^PBoolSet.pprint pb_e1);
  print_endline ("pbools of e2: " ^ Print.pprint e2 ^ ": "^ PBoolSet.pprint pb_e2);
  let prim_bools = PBoolSet.union pb_e1 pb_e2 in
   print_endline ("pbools union: " ^ PBoolSet.pprint prim_bools);
  let atoms = Atom.of_p_bools prim_bools in
   print_endline ("atoms: " ^ Print.pprint_atoms atoms);
  let rec equiv_help ((todo, visited) : PDerivPairSet.t * PDerivPairSet.t) :
      bool =
     print_endline ("TODO:" ^ Print.pprint_pder todo); 
    let new_list = PDerivPairSet.to_list todo in
    let check =
      List.for_all
        (fun (x, y) ->
          (let kx_list = KATSet.to_list x in
           List.is_empty kx_list)
          &&
          let ky_list = KATSet.to_list y in
          List.is_empty ky_list)
        new_list
    in
    (* print_endline (string_of_bool check); *)
    if check then (
      (* print_endline "it is empty!!!"; *)
      true)
    else
      match PDerivPairSet.choose_opt todo with
      (*get a KATSet pair*)
      | None -> true (*todo is empty, finised*)
      | Some (sum1, sum2) ->
           print_endline ("sum1 :" ^ Print.pprint_sum sum1);
          print_endline ("sum2 :" ^ Print.pprint_sum sum2); 
          (*first pair of todo*)
          let h_sum = eps_sum_eq sum1 sum2 atoms in
           print_endline ("eps_sum_eq :" ^ string_of_bool h_sum); 
          if h_sum = false then false (* Eα(E1)!=Eα(E2) *)
          else
            let new_visited = PDerivPairSet.add (sum1, sum2) visited in
            (* add checked pair to visited *)
            let dervs = derivatives prim_bools (sum1, sum2) in
            (*Get rid of pairs of empty lists*)
             print_newline ();
            print_endline ("dervs :" ^ Print.pprint_pder dervs);
            (* find derivs of pair *)
            let new_todo =
              (* add new pairs from derivs to todo and take set diff of visited to avoid reps*)
              PDerivPairSet.diff (PDerivPairSet.union todo dervs) new_visited
            in
             print_endline ("new todo :" ^ Print.pprint_pder new_todo);
            equiv_help (new_todo, new_visited)
    (* first call to equiv_help with todo having e1 and e2 as the first pair and visited as empty pair *)
  in

  equiv_help
    ( PDerivPairSet.singleton (KATSet.singleton e1, KATSet.singleton e2),
      PDerivPairSet.empty )

module Parser = struct
  open Parser.Combinators

  let p_act_parser : katI parser =
    let* start =
      satisfy (fun c -> List.mem c [ 'p'; 'q'; 'r'; 's'; 't'; 'e' ])
    in
    let* rest = many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pAct (implode (start :: rest))) << ws

  let p_bool_parser : katI parser =
    let* start = satisfy (fun c -> List.mem c [ 'a'; 'b'; 'c'; 'd' ]) in
    let* rest = many (satisfy (fun c -> is_alpha c || is_digit c)) in
    pure (pBool (implode (start :: rest))) << ws

  let one_parser : katI parser =
    let* _ = keyword "1" in
    pure one

  let zero_parser : katI parser =
    let* _ = keyword "0" in
    pure zero

  let rec min_term_parser () : katI parser =
    let* _ = pure () in
    choice
      [
        p_act_parser;
        p_bool_parser;
        one_parser;
        zero_parser;
        keyword "(" >> term_parser () << keyword ")";
      ]

  and star_parser () : katI parser =
    let* eI = min_term_parser () in
    let* _ = keyword "*" <|> keyword "^*" in
    pure (star eI)

  and min_term_star_pareser () = star_parser () <|> min_term_parser ()

  and not_pareser () : katI parser =
    let* _ = char '~' << ws in
    let* eI = min_term_star_pareser () << ws in
    pure (not_b eI)

  and not_star_parser () = not_pareser () <|> min_term_star_pareser ()

  and conc_parser () : katI parser =
    let* eI = not_star_parser () in
    let opr () =
      (*conc explicitly using "@" symbol*)
      (let* _ = keyword "@" in
       let* eI = not_star_parser () in
       pure ((fun eI1 eI2 -> conc eI1 eI2), eI))
      <|>
      (*conc implicitly without using any operators*)
      let* eI = not_star_parser () in
      pure ((fun eI1 eI2 -> conc eI1 eI2), eI)
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and union_parser () =
    let* eI = conc_parser () in
    let opr () =
      let* _ = keyword "+" in
      let* eI = conc_parser () in
      pure ((fun eI1 eI2 -> union eI1 eI2), eI)
    in
    let* eIs = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) eI eIs)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  let parse_kat (s : string) : kat option =
    match parse (ws >> term_parser ()) s with
    | Some ((r, _), []) -> Some r
    | _ -> None

  let parse_kat_unsafe (s : string) : kat = Option.get (parse_kat s)
end

(*Examples for testing*)
let fromStr str = Parser.parse_kat_unsafe str

(*
let kat_bpc = fromStr "b(p(c))"
let atom_bc = Atom.of_list [ "b"; "c" ], "p"

let atom_b = Atom.of_list [ "b" ]
let atom_bp = Atom.of_list ["b"], "p"
*)
let neg_kat = Conc (Not (PBool "b1"), PAct "p0")
let trial = Not (PBool"b3")
let trial2 = Conc((Star(Conc(PBool "b3",(Union(Conc(PBool "b1",PAct "p0"),Conc(Not(PBool "b1"),PBool "b2")))))),Not(PBool "b3"))

let t = Star(Conc(Conc(PBool "b1",PBool "b2"),PAct "p0"))

(*let pb = linearization neg_kat*)

(*let exp_b = fromStr "b"
  let exp_bp = fromStr "b(p)"

  let atoms =  Atom.of_list ["a";"b"],"p"
  let x = (linearization (fromStr "b1(p0)"))
  let first = linearization (fromStr "p")
  let second = linearization (fromStr "b(q)")
*)
(**examples to type check /tests**)
(* let rec pBoolOf((exp, expIsBExp): kat * bool):StringSet.t =
     if expIsBExp then
       match exp with           (*At*)
       |One -> StringSet.empty
       |PBool b-> StringSet.singleton b
       |Conc(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))
       |Union(a,b)-> StringSet.union (pBoolOf (a,true)) (pBoolOf (b,true))
       |Not(b) -> pBoolOf (b,true)
       (*TODO: Just to surpress the warning for now, remove when finished*)
       | _ -> failwith "We want boolean expressions but KA expression is given"
   else raise (Invalid_argument "pBool only takes bool expressions") *)

(* OTHER WORK
   let rec epsilon_2 (prim_bools : StringSet.t) (e : kat) : AtomSet.t =
     (*set of atoms*)
     match e with
     | One -> atOf prim_bools
     | Zero -> AtomSet.empty
     | PBool b ->
         atOf (StringSet.remove b prim_bools) |> AtomSet.map (StringSet.add b)
     | PAct _ -> AtomSet.empty (*???*)
     | Union (e1, e2) ->
         let ep1 = epsilon_2 prim_bools e1 and ep2 = epsilon_2 prim_bools e2 in
         AtomSet.union ep1 ep2
     | Conc (e1, e2) ->
         let ep1 = epsilon_2 prim_bools e1 and ep2 = epsilon_2 prim_bools e2 in
         AtomSet.inter ep1 ep2
     | Not e ->
         let atoms = atOf prim_bools and notE = epsilon_2 prim_bools e in
         AtomSet.diff atoms notE
     | Star _ -> atOf prim_bools (*???*)

   (*write hAll version 2 using epsilon_2!!!!!*)
   (*
   let rec h_all_2 (prim_bools:StringSet.t)(s1: KATSet.t)(s2:KATSet.t): bool =
     let e1=KATSet.min_elt s1 in
     let e2=KATSet.min_elt s2 in
     let eps_e1=epsilon_2 prim_bools e1 in
     let eps_e2=epsilon_2 prim_bools e2 in
     if AtomSet.equal eps_e1 eps_e2 then h_all_2 prim_bools (KATSet.remove e1 s1) (KATSet.remove e2 s1)
     else false

    let rec h_all_2_sum (e1:KATSet.t)(e2:KATSet.t)(prim_bools: AtomSet.t): bool =
     if (StringSet.is_empty prim_bools) then true
     else
       let ele = StringSet.min_elt prim_bools in
       if h_all_2 ele e1 e2  then h_all_2_sum e1 e2 (StringSet.remove ele prim_bools)
       else false
   *)
*)
