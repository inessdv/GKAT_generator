(***** Generic Helpers *****)

(** Cartisian product of two lists*)
let list_prod (l : 'a list) (l' : 'b list) : ('a * 'b) list =
  List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l') l)

(** Like powerset but for list
    All the elements in the resulting sub lists maintains their original order.*)
let rec power_list (l : 'a list) : 'a list list =
  let ( let* ) l f = List.concat_map f l in
  match l with
  | [] -> [ [] ]
  | h :: tail ->
      let* sub_tail = power_list tail in
      [ h :: sub_tail; sub_tail ]

(** Monadic map on list with option monad.
  
the map will exit immediately when a None is encountered.
And element that results in Some None will be removed.
This uses difference list technique to keep the map function efficent
https://stackoverflow.com/questions/27386520/tail-recursive-list-map*)
let list_filter_map_m_opt (f : 'a -> 'b option option) (lst : 'a list) :
    'b list option =
  let rec map_aux (acc : 'b list -> 'b list option) : 'a list -> 'b list option
      = function
    | [] -> acc []
    | x :: xs ->
        Option.bind (f x) (fun y_opt ->
            map_aux
              (fun ys ->
                match y_opt with Some y -> acc (y :: ys) | None -> acc ys)
              xs)
  in
  map_aux Option.some lst

(** Given a "recursive function" that compute the one result,
    compute all of the result for each 'a, and arrange in a list,
    the result is in the order of `inp`.

    The first argument of `comp_one_rec` is itself for recursion,
    except the first argument can return None, indicating a finite recursion.
    This function will cache the result of each computation to speed up recursion*)
let compute_map_rec (comp_one_rec : ('a -> 'b option) -> 'a -> 'b)
    (inps : 'a list) : ('a * 'b) list =
  (* the value is marked None, when we are in the process of computing *)
  let memo_tbl : ('a, 'b option) Hashtbl.t =
    Hashtbl.create (List.length inps)
  in
  let rec comp_one_opt inp =
    match Hashtbl.find_opt memo_tbl inp with
    | Some res -> res
    | None ->
        (* Mark that we are currently computing results for `inp`*)
        let () = Hashtbl.add memo_tbl inp None in
        (* recursion *)
        let res = comp_one_rec comp_one_opt inp in
        let () = Hashtbl.replace memo_tbl inp (Some res) in
        Some res
  in
  (* function to compute one result *)
  let compute_one = comp_one_rec comp_one_opt in
  List.map (fun inp -> (inp, compute_one inp)) inps

(** __IMPURE__, like all the queue functions
    Convert a list into a queue*)
let queue_push_list (queue : 'a Queue.t) (l : 'a list) : unit =
  List.iter (fun elem -> Queue.push elem queue) l

(** Helper function to compare two union find elements in options*)
let uf_eq_opt (elem1_opt : 'a UnionFind.elem option)
    (elem2_opt : 'a UnionFind.elem option) =
  match (elem1_opt, elem2_opt) with
  | None, None -> true
  | Some elem1, Some elem2 -> UnionFind.eq elem1 elem2
  | _ -> false

(***** GKAT/GKATI Specific Helpers ******)

type pBool = string
(** Primitive Booleans or Primitive Tests*)

type bExp =
  | PBool of pBool
  | Or of bExp * bExp
  | And of bExp * bExp
  | Zero
  | One
  | Not of bExp

type pAct = string
(** Primitive Actions*)

module PBoolSet = struct
  include Set.Make (String)

  let pprint (pbools : t) : string =
    if is_empty pbools then "{}" else pbools |> to_list |> String.concat "⋅"
end

module Atom = struct
  include Set.Make (String)
  (** Atom is a set of pBools
          all the pBools that is in the set is regarded as positive
          and ones that are not in the set is regarded as negative*)

    let rec of_p_bools (p_bools : PBoolSet.t) : t list =
      match PBoolSet.choose_opt p_bools with
      | None -> [empty]
      | Some p_bool ->
          let atoms_of_rest = of_p_bools (PBoolSet.remove p_bool p_bools) in
          (*atoms that doesn't contain `p_bool`*)
          atoms_of_rest
          @ (*atoms that contains `p_bool`*)
           (atoms_of_rest |> List.map (fun at -> add p_bool at)) 
  let pprint (atom : t) : string =
    if is_empty atom then "{}" else atom |> to_list |> String.concat "⋅"
end

module AtomSet = Set.Make (Atom)

module AtomMap = struct
  include Map.Make (Atom)

  let keys (map : 'a t) : AtomSet.t =
    to_list map |> List.map (fun (key, _) -> key) |> AtomSet.of_list
end

module State = PointedCoprod.MakePosInt

module StatePairSet = Set.Make (struct
  type t = State.t * State.t

  let compare = compare
end)
