(** a kleene datatype, represents regular expressions **)

type 'a kleene =
  | Zero
  | One
  | Value of 'a
  | Union of 'a kleene * 'a kleene
  | Conc of 'a kleene * 'a kleene
  | Star of 'a kleene

(**examples to type check /tests**)
let example1 = Union(Conc(Conc(One,Value('a')),Value('b')), Value('a'))

let example2 = Star(Conc(Star(Conc(Value('a'),Value('b'))),Value('c')))

let example3= Conc(Value '1', Value '8')

let example4 = Union((Conc(Value 'a',Star(Zero))),One)
let example5= Union(Value 'c',Union(Conc(One, Conc(Union(Zero,Value 'a'), Value 'b')), Star(One)))
(**helper funtion to change string to a kleene and kleene to string!**)

module KAParser = struct
  open Parser.Combinators

  let symbol_parser : string kleene parser =
    let* char_list = many1 (satisfy (fun c -> is_alpha c )) in
    let str = implode char_list in
    pure (Value str) << ws
  
  let one_parser : string kleene parser = 
    let* _ = keyword "1" in 
    pure One

  let zero_parser : string kleene parser = 
    let* _ = keyword "0" in 
    pure Zero

  let rec min_term_parser () =
    let* _ = pure () in
    choice
      [ symbol_parser
      ; one_parser
      ; zero_parser
      ; keyword "(" >> term_parser () << keyword ")"
      ]

  and star_parser () = 
    let* e = min_term_parser () in
    let* _ = keyword "*" <|> keyword "^*" in
    pure (Star e)

  and min_term_star_pareser () = star_parser () <|> min_term_parser () 
    
  and conc_parser () : string kleene parser = 
    let* e = min_term_star_pareser () in
    let opr () = 
          (*conc explicitly using "@" symbol*)
          (let* _ = keyword "@" in
          let* e = min_term_star_pareser () in
          pure ((fun e1 e2 -> Conc (e1, e2)), e)) 
          <|>
          (*conc implicitly without using any operators*)
          (let* e = min_term_star_pareser () in
          pure ((fun e1 e2 -> Conc (e1, e2)), e)) 
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and union_parser () =
    let* e = conc_parser () in
    let opr () = (let* _ = keyword "+" in
           let* e = conc_parser () in
           pure ((fun e1 e2 -> Union (e1, e2)), e))
    in
    let* es = many (opr ()) in
    pure (List.fold_left (fun acc (f, e) -> f acc e) e es)

  and term_parser () =
    let* _ = pure () in
    union_parser ()

  let parse_reg (s : string) : string kleene option =
    match parse (ws >> term_parser ()) s with
    |Some (r,[]) -> Some r
    |_ -> None
  let to_string (s) : 'a kleene=
  match s with 
  |Some(a)->a 
  |None -> Zero
end

(** end of parser**)


let rec optimize r = match r  with
  | Zero -> Zero
  | One -> One
  | Value p -> Value p

  | Union (r1,r2) -> let r1 = optimize r1 in let r2 = optimize r2 in 
    (match r1,r2 with 
    (*r1 + (r3 + r4) => (r1 + r3) + r4*)
    | r1, Union (r3, r4) -> 
        Union (Union (optimize r1, optimize r3), optimize r4)
    (*0 + r => r *)
    | Zero,r2 -> r2
    (*r + 0 => r *)
    | r1,Zero -> r1
    (*r + r => r *)
    | r1,r2 -> if r1 == r2 then r1 else Union(r1,r2) )

  | Conc (r1,r2) -> let r1= optimize r1 in let r2= optimize r2 in 
    (match (r1,r2) with 
    (*r1 . (r3 . r4) => (r1 . r3) . r4 *)
    | r1, Conc (r3, r4) -> 
      Conc (Conc (optimize r1, optimize r3), optimize r4)
    (*0 . r => r *)
    | Zero, _ -> Zero
    (*r . 0 => r *)
    | _ ,Zero -> Zero
    (*1 . r => r *)
    | One , r2 -> r2
    (*r . 1 => r *)
    | r1, One -> r1
    (* r* r* => r* *)
    | Star(r1), Star(r2) -> if r1 = r2 then Star(r1) else Conc(r1,r2)
    (* no optimization *)
    | r1, r2 -> Conc(r1,r2) )

  | Star (r1) -> let r1=optimize r1 in 
    (match r1 with
    (* 1* => 1 *)
    | One -> One
    (* 0* => 0 *)
    | Zero -> Zero
    (* no optimization *)
    | r1 -> Star(r1))


module Equiv = struct

  (** epsilon funtion to capture whether the regular expression r contains the empty word**)
  let rec epsilon (r: 'a kleene): bool = match r with
  | One -> true
  | Zero -> false
  | Value _ -> false
  | Union(r1,r2) -> epsilon r1 || epsilon r2
  | Conc(r1,r2) -> epsilon r1 && epsilon r2
  | Star _ -> true

  (** Set of Kleene algebra term, where each symbol is a string*)
  module KASet = Set.Make(struct
    type t = string kleene
    (*uses the default polymorphic compare,
       this only compare the syntax tree, 
       it is not the order in KA*)
    let compare = compare
  end)

  (** Set of string*)
  module StringSet = Set.Make(String)

  (** A map from string*)
  module StringMap = Map.Make(String)

  (** The derivative map, it is a symbol mapped to a set of expression, 
      which are the set representation of derivative with the symbol.*)
  type derMap = KASet.t StringMap.t

  module DerMapSet = Set.Make(struct
    type t = derMap
    let compare = compare
  end)

  module PDerivPairSet = Set.Make (struct
    (* set of pairs of partial derivitives*)
    type t = KASet.t * KASet.t
    let compare = compare
  end) 

  (** Concatate and simplify two expressions,
      this uses algebraic rules of conc to simplify the result*)
  let conc_alg (e1: string kleene) (e2: string kleene): string kleene = 
    match e1, e2 with 
    | One, _ -> e2 
    | _, One -> e1 
    | Zero, _ -> Zero
    | _, Zero -> Zero
    | _, _ -> Conc (e1, e2)

  (** concatenate a regular expression to every regular expressions in the linear form*)
  let conc_der_map (der_map: derMap) (r: string kleene): derMap = 
    StringMap.map (fun derivs -> 
      KASet.map (fun deriv -> conc_alg deriv r) derivs) 
    der_map
    
  (** Create the union of two linear form, 
      this will merge all the deriviative of the same head
      this corresponds to the sum of two linear forms*)
  let union_der_map (lin1: derMap) (lin2: derMap): derMap = 
    StringMap.union 
      (* combine two KA set with union, when their hd are the same*)
      (fun _ s1 s2 -> Some (KASet.union s1 s2))
      lin1 lin2

  (*** do i need a helper function to find head p for r?**)
  (** get_der_map function returning a list of tuples of the head p of regular expression r1 (p,r1)**)
  let rec get_der_map (r: string kleene): derMap = match r with
    | Zero-> StringMap.empty
    | One -> StringMap.empty
    | Value p -> StringMap.singleton p (KASet.singleton One)
    | Union(r1,r2) -> union_der_map (get_der_map r1) (get_der_map r2)
    (* four concatnation cases**)
    | Conc(Value p,r') -> StringMap.singleton p (KASet.singleton r')
    | Conc((Star(r1)),r2) -> 
      union_der_map 
        (conc_der_map (conc_der_map (get_der_map r1) (Star r1)) r2)
        (get_der_map r2)
    | Conc((Union(r1,r2)),r3) -> union_der_map (get_der_map (Conc(r1,r2))) (get_der_map (Conc(r2,r3))) 
    | Conc(Conc(r1,r2),r3) -> get_der_map (Conc(r1,Conc(r2,r3)))
    | Conc(One, r') -> get_der_map r'
    | Conc(Zero, _) -> StringMap.empty
    | Star(r') -> conc_der_map (get_der_map r') (Star(r'))

  (** Get the derivative map for a sum, represented as a set of terms*)
  let get_der_map_sum (sum: KASet.t): DerMapSet.t = 
    KASet.to_seq sum 
    |> Seq.map get_der_map 
    |> DerMapSet.of_seq

  (*** The following functions will help define the decision procedure
      hd(RE) , der_p(RE) , der_ext(P(RE)), ep(RE) , derivatives(R1,R2)
  **)
  (** Function hd(r) to find head**)
  let hd (r: derMap): StringSet.t =
    (*convert the keys into set*)
    StringSet.of_seq (Seq.map fst (StringMap.to_seq r))

  (** Function der_p(RE) -> P(RE) to find **)
  let deriv (p: string) (der_map: derMap): KASet.t = 
    match StringMap.find_opt p der_map with 
    (*If the p doesn't exists then return empty*)
    | None -> KASet.empty
    (*Otherwise return the sum*)
    | Some der_sum -> der_sum

  (** Function eps(P(RE)) checking for empty word
      No longer needed, included in linearize_sum*)
  let eps (sum: KASet.t): bool =
    KASet.exists (fun r -> epsilon r) sum

  (** Function der_ext(P(RE))**)
  let deriv_sum (p: string)(sum_der_map: DerMapSet.t): KASet.t =
    DerMapSet.to_seq sum_der_map 
    (*Take the derivative of each element of the sum*)
    |> Seq.map (deriv p)  
    (*Union the results*)
    |> Seq.fold_left KASet.union KASet.empty 

  (** Function hd_ext, extension of hd to lists of RE**)
  let hd_sum (sum: DerMapSet.t): StringSet.t = 
    let sumList = DerMapSet.to_seq sum in 
    (* union each head of term in the sum*)
    Seq.fold_left StringSet.union StringSet.empty (Seq.map hd sumList)

  (** Function derivatives(R1,R2), findes derivatives of a pair of kleene sets**)
  let derivatives ((r1, r2): KASet.t * KASet.t): PDerivPairSet.t =
    let der_map1 = get_der_map_sum r1 in  
    let der_map2 = get_der_map_sum r2 in
    let heads = StringSet.union (hd_sum der_map1) (hd_sum der_map2) in
    (StringSet.to_seq heads)
    |> (Seq.map (fun p -> (deriv_sum p der_map1, deriv_sum p der_map2)) )
    |> PDerivPairSet.of_seq

(*Equiv function*)
  let rec equiv ((todo, visited): PDerivPairSet.t * PDerivPairSet.t): bool =
      match PDerivPairSet.choose_opt todo with 
      (*todo is empty, finised*)
      | None -> true
      | Some (sum1,sum2) -> 
          if eps(sum1) != eps(sum2) then false else
          let new_visited = PDerivPairSet.add (sum1, sum2) visited in
          let dervs = derivatives (sum1, sum2) in
          let new_todo = 
            PDerivPairSet.diff (PDerivPairSet.union todo dervs) new_visited in
          equiv(new_todo, new_visited)
end
  
(**
    PRINTING METHODS
**)

module Print = struct

  let pprint (exp: char kleene) = 
  (*helper method, takes a expression, output the string, 
      and **the precedence of the outer most expression** *)
  let rec helper (exp: char kleene): string * int = 
    match exp with
    | One -> ("1", 0)
    | Zero -> ("0", 0)
    | Value(c) -> (String.make 1 c, 0)
    | Star(r) -> 
      let (str, precedence) = helper r in 
      if precedence <= 0 then (str^"*", 0) else ("("^str^")*", 0)
    | Conc(r1, r2) ->
      let (str1, precedence1) = helper r1 in 
      let (str2, precedence2) = helper r2 in 
      let str1' = if precedence1 <= 1 then str1 else "("^str1^")" in 
      let str2' = if precedence2 < 1 then str2 else "("^str2^")" in 
      (str1' ^ " " ^ str2', 1)
    | Union(r1, r2) ->
      let (str1, precedence1) = helper r1 in 
      let (str2, precedence2) = helper r2 in 
      let str1' = if precedence1 <= 2 then str1 else "("^str1^")" in 
      let str2' = if precedence2 < 2 then str2 else "("^str2^")" in 
      (str1' ^ " + " ^ str2', 2) 
  in
  let (str, _) = helper exp in str 

  (* pretty printing with equational theory *)
  let eqpprint (exp: char kleene) = pprint (optimize exp)

end
