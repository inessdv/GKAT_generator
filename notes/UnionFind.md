# A UnionFind Based Algorithm For KAT

Ocaml UnionFind Doc: 
- How to Construct a Union Find module: https://v3.ocaml.org/p/unionFind/latest/doc/index.html
- Functions: https://v3.ocaml.org/p/unionFind/latest/doc/UnionFind/index.html
**Note the unionfind data structure is impure, so try to encapsulate its effect**

PseudoCode: 
```Ocaml
(*build the union find module, I am not sure this will work TBH*)
module UF = UnionFind.Make(UnionFind.StoreTransactionalRef)

(*Derivatives As Pairs*)
fun equivCheck (todo: KATPairSets.t) : bool = 
    case Set.chooseopt todo of 
    (*nothing left to check, done*)
    | None -> True 
    (*checking sum1 and sum2*)
    | Some (sum1, sum2) ->
        let rest = KATPairSets.delete (sum1, sum2) todo

        (*they have the same representative hence bisimular,
        only need to check the rest*)
        if UF.eq (UF.make sum1) (UF.make sum2)
            then equivCheck rest
        (*their epsilon is not the same, hence not bisimular*)
        else if ep_sum sum1 != ep_sum sum2 
            then False
        (*check all the derivatives*)
        else 
            (*marks the two derivative as bisimular*)
            let _ = UF.union sum1 sum2 in 
            (*append the derivatives to the rest*)
            let deriv_pairs = deriv_sum_pairs (sum1, sum2) in 
            let new_todo = KATPairSets.union rest deriv_pairs in 
            equivCheck new_todo
```


# A Symbolic Algorithm for GKAT

A Symbolic GKAT automaton is has a transition of the 
following type `State -> (State -> (BExp, PAct)) × BExp`
where `BExp` is the type of boolean expressions, 
`PAct` is the type of primitive actions.
`s ↦ (s' ↦ (ϕ, p), ψ)` means that 
- the state `s` will transition to `s'`
    when given any atom `α ≤ ϕ` and will always execute `p`.
- and the state `s` will all the atoms in `ψ`.
We say that `s` *accepts* `ψ` 
and `s` will *transition* to `s'` with `ϕ` while executing `p`.

```ocaml
type symb_gkat_automaton = {
    states: StateSet.t;
    start: state;
    (*Over parenthesized to avoid ambiguity*)
    tran: state -> ((state -> (b_exp * p_action)) * b_exp)
}
```
We can further optimize this datatype to let each state record 
their reachable state, but this complicates the Thompson's construction.
```ocaml
type symb_gkat_automaton = {
    reachablity_map: StateSet.t StateMap.t;
    start: state;
    tran: state -> ((state -> (b_exp * p_action)) * b_exp)
}
```
where instead of recording all the states, we record all the reachability in a map,
where we say that `s'` is reachable from `s`,
if `(s, s') ↦ (⊥, p)` for any primitive action `p`.
We can still get the set of all states by getting all the keys of `reachablity_map`.

A symbolic GKAT automaton needs to be *deterministic* in the sense that
all the outgoing transition is disjoint: for all state `s`,
- if `s` accepts `ψ` and transition to `s'` via `ϕ`, then `ψ ∧ ϕ ≡ ⊥` in boolean algebra
- given two distinct state `s₁` and `s₂`
    if `s` transition to `s₁` via `ϕ₁` and `s` transition to `s₂` via `ϕ₂`,
    then `ϕ₁ ∧ ϕ₂ ≡ ⊥`  in boolean algebra
**The deterministic property is not enforced by type,** 
**but the algorithm only works when this property is satisfied**

PsedoCode for the algorithm, we use 
`ŝ` to denote start state, `S` to denote set of all state, 
`δ` to denote the transition function;  
and we use `UF` to denote the global union find data structure.
```
Given two automata (S₁, δ₁, ŝ₁) and (S₂, δ₂, ŝ₂):
    let todo = {(ŝ₁, ŝ₂)} 
    for (s₁, s₂) in todo:
        # unpack the transitions
        let (γ₁, ψ₁) = δ₁(s₁)
        let (γ₂, ψ₂) = δ₂(s₂)

        # two states accepts different atoms, return false
        if ψ₁ ≢ ψ₂
            return false
        else 
            let rep₁ = UF.find s₁
            let rep₂ = UF.find s₂
            # already marked as bisimular, continue
            if UF.eq rep₁ rep₂
                then continue
            else 
                # mark as bisimular, and check reachable state
                UF.union s₁ s₂

                for s₁' in reachable s₁
                for s₂' in reachable s₂
                    let (ϕ₁, p₁) = γ₁(s₁')
                    let (ϕ₂, p₂) = γ₂(s₂')

                    # there is no overlap between transition, nothing to do
                    if ϕ₁ ∧ ϕ₂ ≠ ⊥ 
                        then continue

                    # there is overlap, check bisimulation

                    # the first case, contradiction to bisimulation, return false
                    else if p₁ ≠ p₂
                        return false 
                    # no contradiction found yet, add the check for later
                    else 
                        append todo (s₁', s₂')
                            
    # finished all the elements in todo
    return true
```
Note that this function is long and monolithic, 
probably want to split it into several functions,
to keep the function size small.