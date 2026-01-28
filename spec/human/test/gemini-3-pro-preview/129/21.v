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

Fixpoint pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (Nat.eqb r1 r2) (Nat.eqb c1 c2).

Fixpoint mem_pos (p : Pos) (l : list Pos) : bool :=
  match l with
  | [] => false
  | h :: t => if pos_eqb p h then true else mem_pos p t
  end.

Fixpoint dedup_pos (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | h :: t => if mem_pos h t then dedup_pos t else h :: dedup_pos t
  end.

Definition min_list (l : list nat) : nat :=
  match l with
  | [] => 0 
  | h :: t => fold_right Nat.min h t
  end.

Definition filter_pos_by_val (grid : Grid) (val : nat) (ps : list Pos) : list Pos :=
  filter (fun p => Nat.eqb (get_val grid p) val) ps.

Definition all_neighbors (grid : Grid) (ps : list Pos) : list Pos :=
  let raw := flat_map neighbors ps in
  let valid := filter (in_bounds grid) raw in
  dedup_pos valid.

Definition step (grid : Grid) (current_ps : list Pos) : (nat * list Pos) :=
  let next_ps_candidates := all_neighbors grid current_ps in
  let next_vals := map (get_val grid) next_ps_candidates in
  let min_v := min_list next_vals in
  let best_next_ps := filter_pos_by_val grid min_v next_ps_candidates in
  (min_v, best_next_ps).

Fixpoint generate_path (grid : Grid) (k : nat) (current_ps : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let (v, next_ps) := step grid current_ps in
    v :: generate_path grid k' next_ps
  end.

Definition all_positions (grid : Grid) : list Pos :=
  let R := length grid in
  let C := match grid with [] => 0 | r :: _ => length r end in
  flat_map (fun r => map (fun c => (r,c)) (seq 0 C)) (seq 0 R).

Definition find_minimum_path_impl (grid : Grid) (k : nat) : list nat :=
  match k with
  | 0 => []
  | _ =>
    let all_ps := all_positions grid in
    let all_vals := map (get_val grid) all_ps in
    let min_v := min_list all_vals in
    let start_ps := filter_pos_by_val grid min_v all_ps in
    min_v :: generate_path grid (k - 1) start_ps
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[2; 3; 4]; [5; 6; 7]; [8; 9; 1]] in
  let k := 13 in
  let output := [1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.