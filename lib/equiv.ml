(** 
let rec equiv (re: (('a kleene list * 'a kleene list) list) * (('a kleene list * 'a kleene list) list)): bool =
  match re with
  |([],_)-> true
  |(r1,r2)->if (checkEmpty r1)==false then false
  else 
  let r2=unique(r1@r2) 
  in  (*Updated Head*)
  let deri=List.concat(List.map (fun x -> derivatives x) r1) in
  let der= List.fold_left(fun acc x-> if (List.mem x r2) then acc else x::acc) [] deri  (*derivatives after filtering*)
  in equiv (der,r2)

  let rec equiv (re:(('a kleene list * 'a kleene list) list)* (('a kleene list * 'a kleene list) list) ): bool=
  match re with
  |([], _) -> true
  |(r_set,h_set)->
    match r_set with
      | [] -> true
      |r_pair::xs -> 
        match r_pair with
        | (r1,r2) -> 
          if eps (r1) != eps (r2) then false else 
        let h' = (union_list [(r1,r2)] h_set) in
          let s' = List.fold_left (fun acc x -> if (List.mem x h') == false then x::acc else acc) [] (derivatives (r1,r2)) in
            equiv (( union_list xs s'), h')
  
  (** testing purposes
  let s (r: 'a kleene list * 'a kleene list): ('a kleene list * 'a kleene list)list =
    let h' = [r] in 
      match r with
      | (r1,r2) -> List.fold_left (fun acc x -> if (List.mem x h') == false then x::acc else acc) [] (derivatives (r1,r2))
  **)
  **)