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
  | h :: t => fold_right Nat.min h t
  end.

Fixpoint find_pos_in_row (r c : nat) (row : list nat) (val : nat) : list Pos :=
  match row with
  | [] => []
  | x :: xs => if x =? val then (r, c) :: find_pos_in_row r (S c) xs val
               else find_pos_in_row r (S c) xs val
  end.

Fixpoint find_pos_in_grid (r : nat) (grid : Grid) (val : nat) : list Pos :=
  match grid with
  | [] => []
  | row :: rows => find_pos_in_row r 0 row val ++ find_pos_in_grid (S r) rows val
  end.

Definition grid_min (grid : Grid) : nat :=
  min_list (map min_list grid).

Fixpoint pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  (r1 =? r2) && (c1 =? c2).

Fixpoint member (p : Pos) (l : list Pos) : bool :=
  match l with
  | [] => false
  | x :: xs => pos_eqb p x || member p xs
  end.

Fixpoint nodup_pos (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | x :: xs => if member x xs then nodup_pos xs else x :: nodup_pos xs
  end.

Definition step (grid : Grid) (current_pos : list Pos) : (nat * list Pos) :=
  let all_nbs := flat_map neighbors current_pos in
  let valid_nbs := filter (in_bounds grid) all_nbs in
  let vals := map (get_val grid) valid_nbs in
  match vals with
  | [] => (0, [])
  | _ =>
    let next_min := min_list vals in
    let next_ps := filter (fun p => get_val grid p =? next_min) valid_nbs in
    (next_min, nodup_pos next_ps)
  end.

Fixpoint generate_path (grid : Grid) (k : nat) (current_pos : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let (val, next_ps) := step grid current_pos in
    val :: generate_path grid k' next_ps
  end.

Definition find_minimum_path_impl (grid : Grid) (k : nat) : list nat :=
  if k =? 0 then [] else
  let min_v := grid_min grid in
  let start_ps := find_pos_in_grid 0 grid min_v in
  min_v :: generate_path grid (k - 1) start_ps.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[10; 5; 20; 14; 16]; [7; 11; 12; 17; 9]; [13; 19; 1; 15; 8]; [3; 18; 4; 6; 2]; [22; 21; 23; 24; 25]] in
  let k := 10 in
  let output := [1; 4; 1; 4; 1; 4; 1; 4; 1; 4] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.