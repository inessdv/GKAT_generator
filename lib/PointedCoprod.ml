(** This module defines a pointed type with a coproduct operation over finite set

A pointed type is a tuple of a type with a element in the type: (T, elem) s.t. elem ∈ T;  
Coproduct of two finite set S₁, S₂ is denoted S₁ + S₂, 
equipted with the following operations:
- `to_left: S₁ → S₁ + S₂`, which is the left injection
- `to_right: S₂ → S₁ + S₂`, which is the right injection
- `is_left: S₁ + S₂ → bool`, `is_left e` returns whether `e ∈ S₁`
- `from_coprod: S₁ + S₂ → (S₁, S₂) Either`, which distruct the coproduct.

Notice since Ocaml don't have finite type,
so our type annotation is typically imprecise.
Input outside of the domain, is regarded as undefined behavior.
For example, when given a element outside of `S₁`, 
`to_left` can return any result.
*)

module type Pointed = sig
  (** A pointed type*)

  type t

  val elem : t
end

module Coprod = struct
  module type Base = sig
    (** a minimal requirement for coproduct
      
    This is matches the usual definition of coproduct in Set,
    see the definition for `split` and `join` in `PointedCoprod` for detail.*)

    type t

    val pprint: t -> string

    val compare : t -> t -> int
    (** use to generate set and map *)

    module Set : Set.S with type elt = t

    type coprodRes = {
      to_left : t -> t;
      to_right : t -> t;
      from_coprod : t -> (t, t) Either.t;
      is_left : t -> bool;
    }
    (** helper type for the `coprod` function
        
    See doc for `coprod` function for more detail*)

    val coprod : Set.t -> Set.t -> coprodRes
    (** the coproduct of two finite set,
        
    given two finite input set `S1` and `S2`, compute the following functions:
    - `to_left: S1 -> S1 + S2`: the left injection of the coproduct.
    - `to_right: S2 -> S1 + S2`: the right injection of the coproduct.
    - `from_coprod: S1 + S2 -> S1 ∪ S2`: 
        take a element in `S1 + S2`, 
        and convert it back to a element in `S1` or `S2`.
    - `is_left`: given a element in `S1 + S2`, return whether it is a left element.

    all of the above function assumes that they are from the correct domain,
    but they do not check these assertions, for effenciency purpose.
    *)
  end

  module MakePosIntBase : Base with type t = int = struct
    (** coproduct with __positive__ int*)

    include Int
    module Set = Set.Make (Int)

    let pprint n = string_of_int n

    type coprodRes = {
      to_left : t -> t;
      to_right : t -> t;
      from_coprod : t -> (t, t) Either.t;
      is_left : t -> bool;
    }
    (** helper type for the `coprod` function
      
    See doc for `coprod` function for more detail*)

    (** Construct the coproduct for __positive__ int sets
        
    the left of the coproduct remains unchanged, 
    and all the element in the right will be added by the max element on the left,
    hence making them disjoint*)
    let coprod (s1 : Set.t) (_s2 : Set.t) : coprodRes =
      match Set.max_elt_opt s1 with
      (* s1 is empty *)
      | None ->
          {
            to_left = (fun n -> n);
            to_right = (fun n -> n);
            from_coprod = (fun n -> Right n);
            is_left = (fun _ -> false);
          }
      | Some max_left ->
          let is_left e = e <= max_left in
          {
            to_left = (fun n -> n);
            to_right = (fun n -> n + max_left);
            from_coprod =
              (fun n -> if is_left n then Left n else Right (n - max_left));
            is_left;
          }
  end

  module type S = sig
    include Base

    val split : Set.t -> Set.t -> (t -> 'a) -> (t -> 'a) * (t -> 'a)
    (** for B, C ⊆ t, A ⊆ 'a, B -> C -> Hom(B + C, A) -> Hom(B, A) x Hom(C, A)
      
    natrual inverse of `join`. 
    One side of the natrual isomorphism Hom(B + C, A) ≅ Hom(B, A) x Hom(C, A)*)

    val join : Set.t -> Set.t -> (t -> 'a) * (t -> 'a) -> t -> 'a
    (** for B, C ⊆ t_set, A ⊆ 'a, B -> C -> Hom(B, A) x Hom(C, A) -> Hom(B + C, A)
      
    natrual inverse of `split`. 
    One side of the natrual isomorphism Hom(B + C, A) ≅ Hom(B, A) x Hom(C, A)*)

    val coprod_with_dom : Set.t -> Set.t -> coprodRes * Set.t
    (** Compute both the coproduct and the domain of the coproduct,
      
    Given a two finite set `S1` `S2`, 
    the domain of the coproduct is the finite set `S1 + S2`*)
  end

  module Make (Base : Base) : S with type t = Base.t = struct
    (** Construct a coproduct type with additional usefule helpers*)

    include Base

    (** A classical operation of the coproduct operation.  
        
    for B, C ⊆ t, A ⊆ 'a, B -> C -> Hom(B + C, A) -> Hom(B, A) x Hom(C, A)
    Mainly to demonstrate the coproduct construction coincide with the typical definition of coproduct*)
    let split s1 s2 f_coprod =
      let coprod_res = coprod s1 s2 in
      ( (fun n -> f_coprod @@ coprod_res.to_left n),
        fun n -> f_coprod @@ coprod_res.to_right n )

    (** A classical operation of the coproduct operation.  
      
    for B, C ⊆ t_set, A ⊆ 'a, B -> C -> Hom(B, A) x Hom(C, A) -> Hom(B + C, A)
    Mainly to demonstrate the coproduct construction coincide with the typical definition of coproduct*)
    let join s1 s2 (f_left (*: S1 -> A*), f_right (*: S2 -> A*)) =
      let coprod_res = coprod s1 s2 in
      fun n (*n : S1 + S2*) ->
        match coprod_res.from_coprod n with
        | Left n -> f_left n
        | Right n -> f_right n

    let coprod_with_dom s1 s2 =
      let copord_res = coprod s1 s2 in
      ( copord_res,
        Set.union
          (Set.map copord_res.to_left s1)
          (Set.map copord_res.to_right s2) )
  end
end

module type Base = sig
  include Coprod.Base
  include Pointed with type t := t
end

module type S = sig
  include Coprod.S
  include Pointed with type t := t

  val fresh : Set.t -> t
  (** compute a fresh element that is not in the set*)
end

module Make (M : Base) : S with type t = M.t = struct
  include M
  include Coprod.Make (M)

  let fresh s =
    let coprod_res = coprod s (Set.singleton elem) in
    coprod_res.to_right elem
end

module MakePosInt : S with type t = int = struct
  (** pointed coproduct with __positive__ int,
        
    the left of the coproduct remains unchanged, 
    and all the element in the right will be added by the max element on the left,
    hence making them disjoint*)

  include Coprod.Make (Coprod.MakePosIntBase)

  let elem = 1

  (** create a fresh variable by taking the coproduct from the pointed set*)
  let fresh s =
    match Set.max_elt_opt s with None -> elem | Some max -> max + 1
end
