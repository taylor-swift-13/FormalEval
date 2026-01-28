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

Fixpoint min_nat_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => match t with
              | [] => h
              | _ => Nat.min h (min_nat_list t)
              end
  end.

Definition get_vals (grid:Grid) (ps:list Pos) : list nat :=
  map (get_val grid) ps.

Definition pos_eqb (p1 p2 : Pos) : bool :=
  let '(r1, c1) := p1 in
  let '(r2, c2) := p2 in
  andb (Nat.eqb r1 r2) (Nat.eqb c1 c2).

Fixpoint dedup_pos (ps : list Pos) : list Pos :=
  match ps with
  | [] => []
  | p::ps' => if existsb (pos_eqb p) ps' then dedup_pos ps' else p :: dedup_pos ps'
  end.

Fixpoint solve (grid:Grid) (k:nat) (current:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    match current with
    | [] => []
    | _ =>
      let current_vals := get_vals grid current in
      let min_v := min_nat_list current_vals in
      let best_pos := filter (fun p => Nat.eqb (get_val grid p) min_v) current in
      let next_candidates := flat_map neighbors best_pos in
      let valid_next := filter (in_bounds grid) next_candidates in
      let next_unique := dedup_pos valid_next in
      min_v :: solve grid k' next_unique
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
  let starts := map (fun p => match p with | h::_ => h | [] => (0,0) end) (build_starts grid 0) in
  solve grid k starts.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 4; 7]; [2; 5; 8]; [3; 6; 9]] in
  let k := 17 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.