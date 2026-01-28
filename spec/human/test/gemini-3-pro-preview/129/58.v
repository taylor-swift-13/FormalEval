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

(* Optimized implementation to handle larger k and grid sizes efficiently *)

Definition pos_eq_dec (p1 p2 : Pos) : {p1 = p2} + {p1 <> p2}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition all_positions (grid:Grid) : list Pos :=
  let rows := length grid in
  let cols := match grid with [] => 0 | r::_ => length r end in
  flat_map (fun r => map (fun c => (r,c)) (seq 0 cols)) (seq 0 rows).

Definition min_val_in_pos_list (grid:Grid) (ps:list Pos) : option nat :=
  match ps with
  | [] => None
  | p::rest => 
      Some (fold_right (fun p acc => min (get_val grid p) acc) (get_val grid p) rest)
  end.

Definition filter_pos_by_val (grid:Grid) (ps:list Pos) (v:nat) : list Pos :=
  filter (fun p => Nat.eqb (get_val grid p) v) ps.

Definition step_greedy (grid:Grid) (current_pos : list Pos) : (nat * list Pos) :=
  let all_nb := flat_map (fun p => filter (in_bounds grid) (neighbors p)) current_pos in
  match min_val_in_pos_list grid all_nb with
  | None => (0, [])
  | Some m =>
      let next_pos := filter_pos_by_val grid all_nb m in
      (m, nodup pos_eq_dec next_pos)
  end.

Fixpoint solve_greedy (grid:Grid) (k:nat) (current_pos:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
      let (m, next_pos) := step_greedy grid current_pos in
      m :: solve_greedy grid k' next_pos
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  match k with
  | 0 => []
  | S k' =>
      let all_p := all_positions grid in
      match min_val_in_pos_list grid all_p with
      | None => []
      | Some min_v =>
          let start_pos := filter_pos_by_val grid all_p min_v in
          min_v :: solve_greedy grid k' start_pos
      end
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[10; 5; 20; 14; 16]; [7; 11; 12; 17; 9]; [13; 19; 1; 15; 8]; [3; 18; 4; 6; 2]; [22; 21; 23; 24; 25]] in
  let k := 11 in
  let output := [1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.