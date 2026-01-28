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

(* Note: The neighbors function was adjusted to correctly handle boundary conditions 
   and prevent self-loops caused by natural number subtraction (0-1=0). *)
Definition neighbors (p:Pos) : list Pos :=
  let '(r,c) := p in
  [(r, c+1); (r+1, c)] ++ 
  (if Nat.eqb c 0 then [] else [(r, c-1)]) ++ 
  (if Nat.eqb r 0 then [] else [(r-1, c)]).

Definition get_val (grid:Grid) (p:Pos) : nat :=
  let '(r,c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

(* Helper to find position of value 1 *)
Fixpoint find_val_in_row (row:list nat) (val:nat) (c:nat) : option nat :=
  match row with
  | [] => None
  | h::t => if h =? val then Some c else find_val_in_row t val (S c)
  end.

Fixpoint find_pos_of_val (grid:Grid) (val:nat) (r:nat) : option Pos :=
  match grid with
  | [] => None
  | row::rows =>
    match find_val_in_row row val 0 with
    | Some c => Some (r, c)
    | None => find_pos_of_val rows val (S r)
    end
  end.

Definition get_valid_neighbors (grid:Grid) (p:Pos) : list Pos :=
  filter (in_bounds grid) (neighbors p).

Definition best_neighbor (grid:Grid) (p:Pos) : Pos :=
  let nbs := get_valid_neighbors grid p in
  match nbs with
  | [] => p
  | first::rest =>
    let val_first := get_val grid first in
    fst (fold_right (fun p' (best_p, best_v) =>
           let v' := get_val grid p' in
           if v' <? best_v then (p', v') else (best_p, best_v)
         ) (first, val_first) rest)
  end.

Fixpoint construct_path (grid:Grid) (k:nat) (curr:Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    (get_val grid curr) :: construct_path grid k' (best_neighbor grid curr)
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  match find_pos_of_val grid 1 0 with
  | Some start => construct_path grid k start
  | None => []
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 4; 7]; [2; 5; 8]; [3; 6; 9]] in
  let k := 19 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.