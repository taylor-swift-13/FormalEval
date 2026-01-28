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

Fixpoint min_list (l : list nat) : option nat :=
  match l with
  | [] => None
  | h :: t =>
    match min_list t with
    | None => Some h
    | Some m => Some (min h m)
    end
  end.

Fixpoint min_grid (g : Grid) : option nat :=
  match g with
  | [] => None
  | r :: rs =>
    let mr := min_list r in
    let mrs := min_grid rs in
    match mr, mrs with
    | Some a, Some b => Some (min a b)
    | Some a, None => Some a
    | None, Some b => Some b
    | None, None => None
    end
  end.

Fixpoint find_in_row (r_idx : nat) (c_idx : nat) (row : list nat) (v : nat) : list Pos :=
  match row with
  | [] => []
  | x :: xs => 
    (if x =? v then [(r_idx, c_idx)] else []) ++ find_in_row r_idx (S c_idx) xs v
  end.

Fixpoint find_in_grid (r_idx : nat) (g : Grid) (v : nat) : list Pos :=
  match g with
  | [] => []
  | r :: rs => find_in_row r_idx 0 r v ++ find_in_grid (S r_idx) rs v
  end.

Fixpoint pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (r1 =? r2) (c1 =? c2).

Fixpoint remove_dups (l : list Pos) : list Pos :=
  match l with
  | [] => []
  | x :: xs =>
    if existsb (pos_eqb x) xs then remove_dups xs else x :: remove_dups xs
  end.

Definition next_positions (grid : Grid) (curr : list Pos) : (nat * list Pos) :=
  let all_neighbors := flat_map neighbors curr in
  let valid_neighbors := filter (in_bounds grid) all_neighbors in
  let neighbor_vals := map (get_val grid) valid_neighbors in
  match min_list neighbor_vals with
  | None => (0, [])
  | Some min_v =>
    let best_next := filter (fun p => get_val grid p =? min_v) valid_neighbors in
    (min_v, remove_dups best_next)
  end.

Fixpoint run_steps (grid : Grid) (k : nat) (curr : list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let (v, next) := next_positions grid curr in
    v :: run_steps grid k' next
  end.

Definition find_minimum_path_impl (grid : Grid) (k : nat) : list nat :=
  match k with
  | 0 => []
  | _ =>
    match min_grid grid with
    | None => []
    | Some start_val =>
      let starts := find_in_grid 0 grid start_val in
      start_val :: run_steps grid (k - 1) starts
    end
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 4; 7]; [2; 5; 8]; [3; 6; 9]] in
  let k := 20 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.