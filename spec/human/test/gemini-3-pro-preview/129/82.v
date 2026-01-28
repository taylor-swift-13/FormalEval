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

Fixpoint get_val (grid:Grid) (p:Pos) : nat :=
  let '(r,c) := p in
  match nth_error grid r with
  | Some row => match nth_error row c with Some v => v | None => 0 end
  | None => 0
  end.

Fixpoint lex_le (l1 l2 : list nat) : bool :=
  match l1,l2 with
  | [], _ => true
  | _::_, [] => false
  | h1::t1, h2::t2 => (h1 <? h2) || (andb (h1 =? h2) (lex_le t1 t2))
  end.

(* Helpers for efficient greedy path finding *)

Fixpoint contains (l : list Pos) (p : Pos) : bool :=
  match l with
  | [] => false
  | h :: t =>
    let '(r1, c1) := h in
    let '(r2, c2) := p in
    (andb (Nat.eqb r1 r2) (Nat.eqb c1 c2)) || contains t p
  end.

Fixpoint uniquify (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | h :: t => if contains t h then uniquify t else h :: uniquify t
  end.

Fixpoint min_list (l : list nat) : nat :=
  match l with
  | [] => 0 
  | [x] => x
  | x :: xs => Nat.min x (min_list xs)
  end.

Definition all_positions (grid : Grid) : list Pos :=
  let R := length grid in
  let C := match grid with [] => 0 | r :: _ => length r end in
  let rows := seq 0 R in
  let cols := seq 0 C in
  flat_map (fun r => map (fun c => (r, c)) cols) rows.

Definition filter_pos (grid : Grid) (ps : list Pos) (v : nat) : list Pos :=
  filter (fun p => Nat.eqb (get_val grid p) v) ps.

Definition next_step (grid : Grid) (curr_ps : list Pos) : (nat * list Pos) :=
  let all_neighbors := flat_map neighbors curr_ps in
  let valid_neighbors := filter (in_bounds grid) all_neighbors in
  let unique_neighbors := uniquify valid_neighbors in
  match unique_neighbors with
  | [] => (0, [])
  | _ =>
    let vals := map (get_val grid) unique_neighbors in
    let min_v := min_list vals in
    let next_ps := filter_pos grid unique_neighbors min_v in
    (min_v, next_ps)
  end.

Fixpoint solve_greedy (grid : Grid) (k : nat) (curr_ps : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let (v, next_ps) := next_step grid curr_ps in
    v :: solve_greedy grid k' next_ps
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  let all_p := all_positions grid in
  let vals := map (get_val grid) all_p in
  let min_v := min_list vals in
  let start_ps := filter_pos grid all_p min_v in
  match k with
  | 0 => []
  | S k' => min_v :: solve_greedy grid k' start_ps
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 3; 5; 7]; [9; 11; 13; 15]; [2; 4; 6; 8]; [10; 12; 14; 16]] in
  let k := 19 in
  let output := [1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.