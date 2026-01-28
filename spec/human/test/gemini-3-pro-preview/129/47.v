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

Fixpoint range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S p => range p ++ [p]
  end.

Definition all_positions (grid : Grid) : list Pos :=
  let rows := length grid in
  let cols := match grid with [] => 0 | r :: _ => length r end in
  flat_map (fun r => map (fun c => (r, c)) (range cols)) (range rows).

Definition min_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => fold_right Nat.min x xs
  end.

Definition get_min_val_grid (grid : Grid) : nat :=
  let vals := map (get_val grid) (all_positions grid) in
  min_list vals.

Definition filter_pos_by_val (grid : Grid) (ps : list Pos) (v : nat) : list Pos :=
  filter (fun p => get_val grid p =? v) ps.

Fixpoint pos_eqb (p1 p2 : Pos) : bool :=
  match p1, p2 with
  | (r1, c1), (r2, c2) => andb (r1 =? r2) (c1 =? c2)
  end.

Fixpoint dedup (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | x :: xs =>
      if existsb (pos_eqb x) xs then dedup xs else x :: dedup xs
  end.

Definition step_positions (grid : Grid) (current_pos : list Pos) : (nat * list Pos) :=
  let all_neighbors := flat_map neighbors current_pos in
  let valid_neighbors := filter (in_bounds grid) all_neighbors in
  let vals := map (get_val grid) valid_neighbors in
  match vals with
  | [] => (0, []) 
  | _ =>
    let min_v := min_list vals in
    let next_ps := filter_pos_by_val grid valid_neighbors min_v in
    (min_v, dedup next_ps)
  end.

Fixpoint solve_opt (grid : Grid) (k : nat) (current_pos : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
      let (v, next_pos) := step_positions grid current_pos in
      v :: solve_opt grid k' next_pos
  end.

Definition find_minimum_path_impl (grid : Grid) (k : nat) : list nat :=
  match k with
  | 0 => []
  | _ =>
    let min_v := get_min_val_grid grid in
    let starts := filter_pos_by_val grid (all_positions grid) min_v in
    min_v :: solve_opt grid (k - 1) starts
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 5; 9; 13]; [2; 6; 10; 14]; [3; 7; 11; 15]; [4; 8; 12; 16]] in
  let k := 16 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.