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

Definition min_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | h::t => fold_right Nat.min h t
  end.

Fixpoint all_positions_row (r:nat) (c:nat) (len:nat) : list Pos :=
  match len with
  | 0 => []
  | S n => (r,c) :: all_positions_row r (S c) n
  end.

Fixpoint all_positions (g:Grid) (r:nat) : list Pos :=
  match g with
  | [] => []
  | row::gs => all_positions_row r 0 (length row) ++ all_positions gs (S r)
  end.

Definition filter_pos (grid:Grid) (pos_list:list Pos) (target:nat) : list Pos :=
  filter (fun p => Nat.eqb (get_val grid p) target) pos_list.

Fixpoint elem_pos (p:Pos) (l:list Pos) : bool :=
  match l with
  | [] => false
  | q::qs => if andb (Nat.eqb (fst p) (fst q)) (Nat.eqb (snd p) (snd q)) then true else elem_pos p qs
  end.

Fixpoint dedup_pos (l:list Pos) : list Pos :=
  match l with
  | [] => []
  | p::ps => if elem_pos p ps then dedup_pos ps else p :: dedup_pos ps
  end.

Definition get_all_neighbors (grid:Grid) (starts:list Pos) : list Pos :=
  flat_map (fun p => filter (in_bounds grid) (neighbors p)) starts.

Fixpoint solve_greedy (grid:Grid) (k:nat) (current_ends:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let nbs := dedup_pos (get_all_neighbors grid current_ends) in
    match nbs with
    | [] => []
    | _ =>
      let vals := map (get_val grid) nbs in
      let min_v := min_list vals in
      let next_ends := filter_pos grid nbs min_v in
      min_v :: solve_greedy grid k' next_ends
    end
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  match k with
  | 0 => []
  | _ =>
    let all_pos := all_positions grid 0 in
    let vals := map (get_val grid) all_pos in
    let min_v := min_list vals in
    let starts := filter_pos grid all_pos min_v in
    min_v :: solve_greedy grid (k-1) starts
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 4; 7]; [2; 5; 8]; [3; 6; 9]] in
  let k := 21 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.