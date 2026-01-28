Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Definition Grid := list (list nat).
Definition Pos := (nat * nat)%type.

Definition in_bounds (grid : Grid) (p : Pos) : bool :=
  let '(r,c) := p in
  andb (r <? length grid)
       (match nth_error grid r with
        | Some row => c <? length row
        | None => false
        end).

Definition neighbors (p:Pos) : list Pos :=
  let '(r,c) := p in
  [(r, c+1); (r+1, c)] ++ 
  (if Nat.eqb c 0 then [] else [(r, c-1)]) ++ 
  (if Nat.eqb r 0 then [] else [(r-1, c)]).

Fixpoint get_val (grid:Grid) (p:Pos) : nat :=
  let '(r,c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Fixpoint pos_eq (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (r1 =? r2) (c1 =? c2).

Fixpoint pos_in (p:Pos) (l:list Pos) : bool :=
  match l with
  | [] => false
  | q::qs => if pos_eq p q then true else pos_in p qs
  end.

Fixpoint nodup_pos (l:list Pos) : list Pos :=
  match l with
  | [] => []
  | x::xs => if pos_in x xs then nodup_pos xs else x :: nodup_pos xs
  end.

Definition next_positions (grid:Grid) (current:list Pos) : list Pos :=
  let raw := flat_map neighbors current in
  filter (in_bounds grid) raw.

Definition filter_min_val (grid:Grid) (pos_list:list Pos) : (nat * list Pos) :=
  match pos_list with
  | [] => (0, [])
  | p::ps =>
    let init_v := get_val grid p in
    fold_left (fun acc p =>
      let '(curr_min, curr_ps) := acc in
      let v := get_val grid p in
      if v <? curr_min then (v, [p])
      else if v =? curr_min then (curr_min, p::curr_ps)
      else acc
    ) ps (init_v, [p])
  end.

Fixpoint range (n:nat) : list nat :=
  match n with
  | 0 => []
  | S n' => range n' ++ [n']
  end.

Definition all_grid_positions (grid:Grid) : list Pos :=
  let R := length grid in
  let C := match grid with [] => 0 | r::_ => length r end in
  let rows := range R in
  let cols := range C in
  flat_map (fun r => map (fun c => (r,c)) cols) rows.

Fixpoint greedy_path (grid:Grid) (k:nat) (current:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let '(min_v, best_pos) := filter_min_val grid current in
    let unique_best := nodup_pos best_pos in
    let next_candidates := next_positions grid unique_best in
    min_v :: greedy_path grid k' next_candidates
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  if k =? 0 then [] else
  let all_pos := all_grid_positions grid in
  let '(min_v, start_pos) := filter_min_val grid all_pos in
  let unique_start := nodup_pos start_pos in
  let next_candidates := next_positions grid unique_start in
  min_v :: greedy_path grid (k-1) next_candidates.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[2; 3; 4]; [5; 6; 7]; [8; 9; 1]] in
  let k := 18 in
  let output := [1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.