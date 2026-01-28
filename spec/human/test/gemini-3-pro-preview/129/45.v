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

Definition pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (Nat.eqb r1 r2) (Nat.eqb c1 c2).

Fixpoint dedup (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | x :: xs => if existsb (pos_eqb x) xs then dedup xs else x :: dedup xs
  end.

Definition all_coords (rows cols : nat) : list Pos :=
  flat_map (fun r => map (fun c => (r,c)) (seq 0 cols)) (seq 0 rows).

Definition get_min_val (grid:Grid) (coords:list Pos) : nat :=
  match coords with
  | [] => 0
  | p::ps => fold_right (fun p acc => Nat.min (get_val grid p) acc) (get_val grid p) ps
  end.

Definition filter_min (grid:Grid) (coords:list Pos) (m:nat) : list Pos :=
  filter (fun p => Nat.eqb (get_val grid p) m) coords.

Fixpoint greedy_path (grid:Grid) (k:nat) (current:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
      let m := get_min_val grid current in
      let keepers := filter_min grid current m in
      let nexts := dedup (flat_map neighbors keepers) in
      let nexts_valid := filter (in_bounds grid) nexts in
      m :: greedy_path grid k' nexts_valid
  end.

Fixpoint lex_le (l1 l2 : list nat) : bool :=
  match l1,l2 with
  | [], _ => true
  | _::_, [] => false
  | h1::t1, h2::t2 => (h1 <? h2) || (andb (h1 =? h2) (lex_le t1 t2))
  end.

Fixpoint extend_paths (grid:Grid) (k:nat) (fuel:nat) (paths:list (list Pos)) : list (list Pos) :=
  match fuel with
  | 0 => paths
  | S f' =>
    if k <=? 1 then paths else
    let ex :=
      fold_right (fun p acc =>
        match p with
        | [] => acc | q::_ =>
          fold_right (fun nb acc2 => if in_bounds grid nb then (nb::p)::acc2 else acc2)
                     acc (neighbors q)
        end) [] paths in
    extend_paths grid (k-1) f' ex
  end.

Definition get_path_values (grid:Grid) (path:list Pos) : list nat := map (get_val grid) (rev path).

(* Note: best_by_lex was adjusted to handle the base case where candidates list is exhausted,
   ensuring the last remaining candidate is returned rather than an empty list. *)
Fixpoint best_by_lex (grid:Grid) (candidates:list (list Pos)) : list nat :=
  match candidates with
  | [] => []
  | p::ps =>
    let v := get_path_values grid p in
    match ps with
    | [] => v
    | _ =>
      let best_rest := best_by_lex grid ps in
      if lex_le v best_rest then v else best_rest
    end
  end.

Fixpoint build_row_starts (r:nat) (row:list nat) (c:nat) : list (list Pos) :=
  match row with
  | [] => []
  | _::t => [(r,c)] :: build_row_starts r t (S c)
  end.

Fixpoint build_starts (g:Grid) (r:nat) : list (list Pos) :=
  match g with
  | [] => []
  | row::gs => build_row_starts r row 0 ++ build_starts gs (S r)
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  let rows := length grid in
  let cols := match grid with [] => 0 | r::_ => length r end in
  let starts := all_coords rows cols in
  greedy_path grid k starts.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[2; 3; 4]; [5; 6; 7]; [8; 9; 1]] in
  let k := 15 in
  let output := [1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1; 7; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.