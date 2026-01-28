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

Fixpoint range (n:nat) : list nat :=
  match n with
  | 0 => []
  | S p => range p ++ [p]
  end.

Definition all_positions (grid:Grid) : list Pos :=
  let rows := length grid in
  let cols := match grid with [] => 0 | r::_ => length r end in
  let r_indices := range rows in
  let c_indices := range cols in
  flat_map (fun r => map (fun c => (r,c)) c_indices) r_indices.

Definition pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1,c1) := p1 in
  let '(r2,c2) := p2 in
  andb (Nat.eqb r1 r2) (Nat.eqb c1 c2).

Fixpoint nodup_pos (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | x::xs => if existsb (pos_eqb x) xs then nodup_pos xs else x :: nodup_pos xs
  end.

Definition step_greedy (grid:Grid) (current_pos : list Pos) : (nat * list Pos) :=
  let all_next := nodup_pos (flat_map neighbors current_pos) in
  let valid_next := filter (in_bounds grid) all_next in
  match valid_next with
  | [] => (0, [])
  | p::ps =>
    let vals := map (fun x => (get_val grid x, x)) valid_next in
    let min_val := fold_right (fun '(v,_) acc => Nat.min v acc) (get_val grid p) vals in
    let next_pos := filter (fun x => Nat.eqb (get_val grid x) min_val) valid_next in
    (min_val, next_pos)
  end.

Fixpoint loop_greedy (grid:Grid) (k:nat) (current_pos : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let (v, next_pos) := step_greedy grid current_pos in
    v :: loop_greedy grid k' next_pos
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  match k with
  | 0 => []
  | _ =>
    let all_pos := all_positions grid in
    match all_pos with
    | [] => []
    | p::ps =>
       let vals := map (fun x => (get_val grid x, x)) all_pos in
       let min_val := fold_right (fun '(v,_) acc => Nat.min v acc) (get_val grid p) vals in
       let start_pos := filter (fun x => Nat.eqb (get_val grid x) min_val) all_pos in
       min_val :: loop_greedy grid (pred k) start_pos
    end
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 4; 7]; [2; 5; 8]; [3; 6; 9]] in
  let k := 14 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.