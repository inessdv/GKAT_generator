open Common
open GKAT_2
open PointedCoprod
module PActSet = Set.Make (String)
module StateMap = Map.Make (State)

type state_set_map = State.Set.t StateMap.t
type res = Accept | Reject | To of State.t * pAct
type trans = State.t -> Atom.t -> res

module Automaton = struct
  type t = {
    p_tests : PBoolSet.t;
    p_acts : PActSet.t;
    states : State.Set.t;
    trans : trans;
    start : State.t;
  }
end

module PAutomaton = struct
  type t = {
    p_tests : PBoolSet.t;
    p_acts : PActSet.t;
    states : State.Set.t;
    trans : trans;
    p_start : Atom.t -> res;
  }
end

module AutomatonPrinter = struct
  let string_of_string_list lst =
    let rec aux = function
      | [] -> ""
      | [ x ] -> x
      | x :: xs -> x ^ "; " ^ aux xs
    in
    "[" ^ aux lst ^ "]"

  let setListPrinter (set_list : PActSet.t list) =
    let list_of_list = List.map (fun ele -> PActSet.to_list ele) set_list in
    let single_list =
      List.map (fun ele -> string_of_string_list ele) list_of_list
    in
    string_of_string_list single_list

  let string_of_statemap_list lst =
    let rec aux = function
      | [] -> ""
      | [ (x, _y) ] -> "(" ^ string_of_int x ^ " , " ^ " y " ^ ")"
      | (x, _y) :: xs ->
          "(" ^ string_of_int x ^ " , " ^ " y " ^ ")" ^ "; " ^ aux xs
    in
    "[" ^ aux lst ^ "]"

  let statemap_printer m =
    let map_list = StateMap.to_list m in
    string_of_statemap_list map_list

  (* Convert a single integer pair to a string *)
  let string_of_int_pair (x, y) = Printf.sprintf "(%d, %d)" x y

  (* Convert a list of integer pairs to a string *)
  let string_of_int_pair_list lst =
    let pairs_str =
      List.map string_of_int_pair lst
      |> String.concat "; " (* Use "; " to separate pairs *)
    in
    "[" ^ pairs_str ^ "]"

  let statepairSet_printer m =
    let l = StatePairSet.to_list m in
    string_of_int_pair_list l

  let int_list_to_string lst =
    (* Convert each integer to a string and join them with ", " *)
    let string_list = List.map string_of_int lst in
    String.concat ", " string_list

  let stateset_printer m =
    let l = MakePosInt.Set.to_list m in
    int_list_to_string l

  let string_of_res = function
    | Accept -> "Accept"
    | Reject -> "Reject"
    | To (state, pAct) ->
        Printf.sprintf "To (%s, %s)" (string_of_int state) pAct

  let string_of_trans (a : Automaton.t) =
    (* Assuming a function to iterate over all possible state-atom pairs *)
    let trans = a.trans in
    let atoms = Atom.of_p_bools a.p_tests in
    let buffer = Buffer.create 1024 in
    State.Set.iter
      (fun state ->
        List.iter
          (fun atom ->
            let result = trans state atom in
            Buffer.add_string buffer
              (Printf.sprintf "trans(%s, %s) = %s\n" (string_of_int state)
                 (string_of_string_list (PActSet.to_list atom))
                 (string_of_res result)))
          atoms)
      a.states;
    Buffer.contents buffer

  let string_of_ptrans (a : PAutomaton.t) =
    (* Assuming a function to iterate over all possible state-atom pairs *)
    let trans = a.trans in
    let atoms = Atom.of_p_bools a.p_tests in
    let buffer = Buffer.create 1024 in
    State.Set.iter
      (fun state ->
        List.iter
          (fun atom ->
            let result = trans state atom in
            Buffer.add_string buffer
              (Printf.sprintf "trans(%s, %s) = %s\n" (string_of_int state)
                 (string_of_string_list (PActSet.to_list atom))
                 (string_of_res result)))
          atoms)
      a.states;
    Buffer.contents buffer

  let string_of_p_start (a : PAutomaton.t) =
    let buffer = Buffer.create 1024 in
    let atoms = Atom.of_p_bools a.p_tests in
    List.iter
      (fun atom ->
        let result = a.p_start atom in
        Buffer.add_string buffer
          (Printf.sprintf "p_start(%s) = %s\n"
             (string_of_string_list (PActSet.to_list atom))
             (string_of_res result)))
      atoms;
    Buffer.contents buffer

  let print_automaton (automaton : Automaton.t) =
    let states_str = stateset_printer automaton.states in
    let p_tests_str =
      string_of_string_list (PBoolSet.to_list automaton.p_tests)
    in
    let p_acts_str = string_of_string_list (PActSet.to_list automaton.p_acts) in
    let start_str = string_of_int automaton.start in
    let trans_str = string_of_trans automaton in

    Printf.printf "Automaton:\n";
    Printf.printf "States: %s\n" states_str;
    Printf.printf "P_Tests: %s\n" p_tests_str;
    Printf.printf "P_Actions: %s\n" p_acts_str;
    Printf.printf "Start State: %s\n" start_str;
    Printf.printf "Transitions:\n%s\n" trans_str
  (* let automaton_printer (a: Automaton.t) =
      let atoms = Atom.of_p_bools a.p_tests in
      let states = a.states in
      List.iter(fun (s) -> ) *)

  let print_Pautomaton (automaton : PAutomaton.t) =
    let states_str = stateset_printer automaton.states in
    let p_tests_str =
      string_of_string_list (PBoolSet.to_list automaton.p_tests)
    in
    let p_acts_str = string_of_string_list (PActSet.to_list automaton.p_acts) in
    let start_str = string_of_p_start automaton in
    let trans_str = string_of_ptrans automaton in

    Printf.printf "PAutomaton:\n";
    Printf.printf "States: %s\n" states_str;
    Printf.printf "P_Tests: %s\n" p_tests_str;
    Printf.printf "P_Actions: %s\n" p_acts_str;
    Printf.printf "Start State: %s\n" start_str;
    Printf.printf "Transitions:\n%s\n" trans_str

  let print_from_auto_option (automaton : Automaton.t option) =
    match automaton with
    | Some a -> print_automaton a
    | None -> print_endline "None"

  (* Convert a (int * intSet) tuple to a string *)
  let string_of_int_intset_tuple (i, set) =
    "(" ^ string_of_int i ^ " -> " ^ stateset_printer set ^ ")"

  (* Convert a list of (int * intSet) to a string *)
  let state_set_map_printer (lst : state_set_map) =
    let l = StateMap.to_list lst in
    let string_elements = List.map string_of_int_intset_tuple l in
    "[" ^ String.concat "; " string_elements ^ "]"
end

let res_to_left (r : res) (coprod : MakePosInt.coprodRes) : res =
  match r with
  | Accept -> Accept
  | Reject -> Reject
  | To (s, p_act) -> To (coprod.to_left s, p_act)

let res_to_right (r : res) (coprod : MakePosInt.coprodRes) : res =
  match r with
  | Accept -> Accept
  | Reject -> Reject
  | To (s, p_act) -> To (coprod.to_right s, p_act)

let rec satisfy (at : Atom.t) (iota : bExp) : bool =
  match iota with
  | Zero -> false
  | One -> true
  | PBool b -> Atom.mem b at
  | Or (i, b) -> satisfy at i || satisfy at b
  | And (i, b) -> satisfy at i && satisfy at b
  | Not b -> not (satisfy at b)

let rec thompson_construct (exp : gkat) (p_act : PActSet.t)
    (p_test : PBoolSet.t) : PAutomaton.t =
  match exp with
  | Pact p ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.singleton State.elem;
        trans = (fun _ _ -> Accept);
        p_start = (fun _ -> To (State.elem, p));
      }
  | Seq (exp1, exp2) ->
      let auto1 = thompson_construct exp1 p_act p_test in
      let auto2 = thompson_construct exp2 p_act p_test in
      let coprod, all_states =
        State.coprod_with_dom auto1.states auto2.states
      in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans =
          (fun state atom ->
            match coprod.from_coprod state with
            | Right s -> res_to_right (auto2.trans s atom) coprod
            | Left s -> (
                match auto1.trans s atom with
                | Accept -> res_to_right (auto2.p_start atom) coprod
                | r -> res_to_left r coprod));
        p_start =
          (fun at ->
            match auto1.p_start at with
            | Accept -> res_to_right (auto2.p_start at) coprod
            | r -> r);
      }
  | If (bexp, exp1, exp2) ->
      let auto1 = thompson_construct exp1 p_act p_test in
      let auto2 = thompson_construct exp2 p_act p_test in
      let coprod, all_states =
        State.coprod_with_dom auto1.states auto2.states
      in
      {
        p_tests = p_test;
        p_acts = p_act;
        states = all_states;
        trans =
          (fun state atom ->
            match coprod.from_coprod state with
            | Right s -> res_to_right (auto2.trans s atom) coprod
            | Left s -> res_to_left (auto1.trans s atom) coprod);
        p_start =
          (fun atom ->
            if satisfy atom bexp then res_to_left (auto1.p_start atom) coprod
            else res_to_right (auto2.p_start atom) coprod);
      }
  | Test b ->
      {
        p_tests = p_test;
        p_acts = p_act;
        states = State.Set.empty;
        trans = (fun _ -> failwith "no result");
        p_start = (fun at -> if satisfy at b then Accept else Reject);
      }
  | While (bexp, exp) ->
      let auto1 = thompson_construct exp p_act p_test in
      let iota_e atom =
        if satisfy atom bexp then
          match auto1.p_start atom with
          | Accept -> Reject
          | _ -> auto1.p_start atom
        else Accept
      in

      {
        p_tests = p_test;
        p_acts = p_act;
        states = auto1.states;
        trans =
          (fun state atom ->
            match auto1.trans state atom with Accept -> iota_e atom | r -> r);
        p_start = iota_e;
      }

let convertFromPautomatonToAutomaton (pauto : PAutomaton.t) : Automaton.t =
  let newStart = State.fresh pauto.states in
  {
    p_tests = pauto.p_tests;
    p_acts = pauto.p_acts;
    states = State.Set.add newStart pauto.states;
    trans =
      (fun state atom ->
        match state == newStart with
        (*If statement*)
        | true -> pauto.p_start atom
        | false -> pauto.trans state atom);
    start = newStart;
  }

let check_res (res1 : res) (res2 : res) : StatePairSet.t option =
  match (res1, res2) with
  | Accept, Accept -> Some StatePairSet.empty
  | Reject, Reject -> Some StatePairSet.empty
  | To (s1, p1), To (s2, p2) ->
      let s_pair = StatePairSet.singleton (s1, s2) in
      if p1 = p2 then Some s_pair else None
  | _ -> None

let rec check_atoms ((s1, s2) : State.t * State.t)
    (atoms_toCheck : PActSet.t list) (a1 : Automaton.t) (a2 : Automaton.t) :
    StatePairSet.t option =
  match atoms_toCheck with
  | [] -> Some StatePairSet.empty
  | atom :: rest -> (
      match check_res (a1.trans s1 atom) (a2.trans s2 atom) with
      | None -> None
      | Some s_pairs -> (
          match check_atoms (s1, s2) rest a1 a2 with
          | None -> None
          | Some s_pairs1 -> Some (StatePairSet.union s_pairs s_pairs1)))

let bisimimulation (a1 : Automaton.t) (a2 : Automaton.t) : bool =
  (* print_endline "Asserting a1.p_tests = a2.p_tests"; *)
  assert (a1.p_tests = a2.p_tests);
  (* print_endline "Succeeded Asserting a1.p_tests = a2.p_tests"; *)
  let atoms = Atom.of_p_bools a1.p_tests in
  (* print_endline
    ("The Atom.of_p_bools a1.p_tests is  "
    ^ AutomatonPrinter.setListPrinter atoms); *)
  (* maps each state in a1 to its corresponding unionfind element *)
  let uf_map1 =
    List.map (fun s -> (s, UnionFind.make s)) (a1.states |> State.Set.to_list)
    |> StateMap.of_list
  in
  (* print_endline
    ("the Statemap of a1's states is "
    ^ AutomatonPrinter.statemap_printer uf_map1); *)
  let uf_map2 =
    List.map (fun s -> (s, UnionFind.make s)) (a2.states |> State.Set.to_list)
    |> StateMap.of_list
  in
  (* print_endline
    ("the Statemap of a2's states is "
    ^ AutomatonPrinter.statemap_printer uf_map2); *)
  (* get union find element of automaton 1*)
  let get_elem1 s = StateMap.find s uf_map1 in
  let get_elem2 s = StateMap.find s uf_map2 in
  (*is this issue?*)
  let rec help (todo : StatePairSet.t) : bool =
    match StatePairSet.choose_opt todo with
    | None ->
        (* print_endline "";
        print_endline "Equiv asserted";
        print_endline ""; *)
        true
    | Some (s1, s2) -> (
        if
          (* if they are already marked bisimilar *)
          (* print_endline
            ("The s1 is " ^ string_of_int s1 ^ " The s2 is " ^ string_of_int s2); *)
          UnionFind.eq (get_elem1 s1) (get_elem2 s2)
        then help (StatePairSet.remove (s1, s2) todo)
          (*Edited: Should not return true, should filter and continue*)
        else
          (* add check_atoms inside function to avoid passing a1 and a2??*)
          match check_atoms (s1, s2) atoms a1 a2 with
          | None ->
              (* print_endline "check_atom returns false"; *)
              false
          | Some to_check ->
              (* print_endline
                ("to_check:" ^ AutomatonPrinter.statepairSet_printer to_check); *)
              (* remove all the checked equal states *)
              let to_check =
                StatePairSet.filter
                  (fun (state1, state2) ->
                    not @@ UnionFind.eq (get_elem1 state1) (get_elem2 state2))
                  to_check
              in
              (* print_endline
                ("to_check after: "
                ^ AutomatonPrinter.statepairSet_printer to_check); *)
              ignore @@ UnionFind.union (get_elem1 s1) (get_elem2 s2);
              (* print_endline
                ("the new todo is "
                ^ AutomatonPrinter.statepairSet_printer
                    (StatePairSet.union to_check todo)); *)
              help (StatePairSet.union to_check todo))
  in
  let start_pair = StatePairSet.singleton (a1.start, a2.start) in
  help start_pair

(*Cartesian product for two lists*)
let product (l1 : 'a list) (l2 : 'b list) : ('a * 'b) list =
  List.rev
    (List.fold_left
       (fun x a -> List.fold_left (fun y b -> (a, b) :: y) x l2)
       [] l1)

(*The result map won't include the start state, because no state transits to the start state*)
let rev_map (a : Automaton.t) : State.Set.t StateMap.t =
  let states = a.states in
  let atoms = Atom.of_p_bools a.p_tests in
  let state_atom_pairs = product (State.Set.to_list states) atoms in

  let statesPair_list =
    List.filter_map
      (fun (s, at) ->
        match a.trans s at with To (s', _) -> Some (s', s) | _ -> None)
      state_atom_pairs
  in

  List.fold_left
    (fun m (s', s) ->
      StateMap.update s'
        (fun opt ->
          match opt with
          | Some state -> Some (State.Set.add s state)
          | None -> Some (State.Set.singleton s))
        m)
    StateMap.empty statesPair_list

(*DFS to get live states*)
let rec live_states_from (graph : state_set_map) (state : State.t)
    (visited : State.Set.t) : State.Set.t =
  (* print_endline ("checking live states from " ^ State.pprint state); *)
  if State.Set.mem state visited then visited
  else
    (*check if we have checked this state*)
    let new_visited = State.Set.add state visited in
    match StateMap.find_opt state graph with
    | Some states ->
        let x =
          State.Set.fold
            (fun s acc -> live_states_from graph s acc)
            states new_visited
        in
        (* print_endline ("x is " ^ stateset_printer x); *)
        x
    | None ->
        (* print_endline ("new_visited is " ^ stateset_printer new_visited); *)
        new_visited

(*Getting all accepting states from an automaton*)
let get_accpeting_states_from (a : Automaton.t) (atoms : PBoolSet.t list) :
    State.Set.t =
  let states = a.states in
  State.Set.filter
    (fun s -> List.exists (fun at -> a.trans s at = Accept) atoms)
    states

let normalization (a : Automaton.t) : Automaton.t =
  let atoms = Atom.of_p_bools a.p_tests in
  let accepting_states = get_accpeting_states_from a atoms in
  (* print_endline
     ("The accepting states are " ^ stateset_printer accepting_states); *)
  let reverse_auto = rev_map a in
  (* print_endline ("The reverse map is " ^ state_set_map_printer reverse_auto); *)
  (*for each accept state DFS to check for other live states*)
  let live_states =
    State.Set.fold
      (fun s acc -> live_states_from reverse_auto s acc)
      accepting_states State.Set.empty
  in
  (* print_endline ("The live states are " ^ stateset_printer live_states); *)
  (*Updating res of transition function to reject if To dead state*)
  {
    a with
    trans =
      (fun state atom ->
        match a.trans state atom with
        | To (s, p) -> if State.Set.mem s live_states then To (s, p) else Reject
        | res -> res);
  }

let rec be_to_pbool (be : bExp) (p_bool : PBoolSet.t) : PBoolSet.t =
  match be with
  | GKAT_2.Zero -> p_bool
  | GKAT_2.One -> p_bool
  | GKAT_2.PBool b -> PBoolSet.add b p_bool
  | GKAT_2.Or (be1, be2) ->
      PBoolSet.union (be_to_pbool be1 p_bool) (be_to_pbool be2 p_bool)
  | GKAT_2.And (be1, be2) ->
      PBoolSet.union (be_to_pbool be1 p_bool) (be_to_pbool be2 p_bool)
  | GKAT_2.Not be -> PBoolSet.union p_bool (be_to_pbool be p_bool)

let rec extract_p_act (exp : gkat) (p_act : PActSet.t) : PActSet.t =
  match exp with
  | Pact p -> PActSet.add p p_act
  | Seq (exp1, exp2) ->
      PActSet.union (extract_p_act exp1 p_act) (extract_p_act exp2 p_act)
  | If (_, exp1, exp2) ->
      PActSet.union (extract_p_act exp1 p_act) (extract_p_act exp2 p_act)
  | Test _ -> p_act
  | While (_, exp) -> PActSet.union p_act (extract_p_act exp p_act)

let rec extract_p_bool (exp : gkat) (p_bool : PBoolSet.t) : PBoolSet.t =
  match exp with
  | Pact _ -> p_bool
  | Seq (exp1, exp2) ->
      PBoolSet.union (extract_p_bool exp1 p_bool) (extract_p_bool exp2 p_bool)
  | If (be, exp1, exp2) ->
      PBoolSet.union
        (be_to_pbool be PBoolSet.empty)
        (PBoolSet.union
           (extract_p_bool exp1 p_bool)
           (extract_p_bool exp2 p_bool))
  | Test be -> PBoolSet.union (be_to_pbool be PBoolSet.empty) p_bool
  | While (be, exp) ->
      PBoolSet.union
        (be_to_pbool be PBoolSet.empty)
        (PBoolSet.union p_bool (extract_p_bool exp p_bool))

let equiv (exp1 : gkat) (exp2 : gkat) : bool =
  let p_bool =
    PBoolSet.union
      (extract_p_bool exp1 PBoolSet.empty)
      (extract_p_bool exp2 PBoolSet.empty)
  in
  let p_act =
    PActSet.union
      (extract_p_act exp1 PActSet.empty)
      (extract_p_act exp2 PActSet.empty)
  in
  let auto1 =
    normalization
      (convertFromPautomatonToAutomaton (thompson_construct exp1 p_act p_bool))
  in

  (* print_endline "The auto1's Pautomaton is ";
  AutomatonPrinter.print_Pautomaton (thompson_construct exp1 p_act p_bool);
  print_endline "The auto1's automaton is ";
  AutomatonPrinter.print_automaton
    (convertFromPautomatonToAutomaton (thompson_construct exp1 p_act p_bool));
  print_endline "The auto1's filtered automaton is";
  AutomatonPrinter.print_automaton auto1; *)
  let auto2 =
    normalization
      (convertFromPautomatonToAutomaton (thompson_construct exp2 p_act p_bool))
  in

  (* print_endline "The auto2's Pautomaton is ";
  AutomatonPrinter.print_Pautomaton (thompson_construct exp2 p_act p_bool);
  print_endline "The auto2's automaton is ";
  AutomatonPrinter.print_automaton
    (convertFromPautomatonToAutomaton (thompson_construct exp2 p_act p_bool));
  print_endline "The auto2's filtered automaton is";
  AutomatonPrinter.print_automaton auto2; *)
  bisimimulation auto1 auto2

(* let gkat_example1 =
     Seq
       ( Seq
           ( Pact "p7",
             If
               ( PBool "b2",
                 p_act "p6",
                 Seq (test (Not (PBool "b2")), test (Not (PBool "b1"))) ) ),
         test (Not (PBool "b1")) )

   let gkat_example2 = Seq(Pact "p7" , Pact "p5") *)

(*if b3 and b2 then if ~b3 then b1 else p4 else (p4 * ~b2) * while b3 do (b1 or b3 * (~b1 * p5)) done EXP2: p4 (after 3 shrink steps)*)
(* let gkat_example1 =
     If
       ( And (PBool "b2", PBool "b3"),
         If (Not (PBool "b3"), test (PBool "b1"), Pact "p4"),
         Seq
           ( Seq (Pact "p4", test (Not (PBool "b2"))),
             While
               ( PBool "b3",
                 Seq
                   ( test (Or (PBool "b1", PBool "b3")),
                     Seq (test (Not (PBool "b1")), Pact "p5") ) ) ) )
   let gkat_example2= Pact "p4" *)
