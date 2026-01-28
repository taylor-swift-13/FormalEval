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

Fixpoint enumerate_row (r:nat) (c:nat) (row:list nat) : list (Pos * nat) :=
  match row with
  | [] => []
  | x::xs => ((r,c), x) :: enumerate_row r (S c) xs
  end.

Fixpoint enumerate_grid (r:nat) (g:Grid) : list (Pos * nat) :=
  match g with
  | [] => []
  | row::rows => enumerate_row r 0 row ++ enumerate_grid (S r) rows
  end.

Definition get_next_step (grid:Grid) (tips:list Pos) : nat * list Pos :=
  let all_nbs := flat_map neighbors tips in
  let valid_nbs := filter (in_bounds grid) all_nbs in
  let vals := map (fun p => (p, get_val grid p)) valid_nbs in
  match vals with
  | [] => (0, [])
  | (p,v)::t =>
    fold_left (fun (acc:nat*list Pos) (x:Pos*nat) =>
      let '(min_v, ps) := acc in
      let '(p', v') := x in
      if v' <? min_v then (v', [p'])
      else if v' =? min_v then (min_v, p'::ps)
      else acc)
    t (v, [p])
  end.

Fixpoint run_greedy (grid:Grid) (k:nat) (tips:list Pos) : list nat :=
  match k with
  | 0 => []
  | S k' =>
    let '(v, next_tips) := get_next_step grid tips in
    v :: run_greedy grid k' next_tips
  end.

Definition find_minimum_path_impl (grid:Grid) (k:nat) : list nat :=
  let all := enumerate_grid 0 grid in
  match all with
  | [] => []
  | (p,v)::t =>
    let '(min_v, starts) := 
      fold_left (fun (acc:nat*list Pos) (x:Pos*nat) =>
        let '(min_v, ps) := acc in
        let '(p', v') := x in
        if v' <? min_v then (v', [p'])
        else if v' =? min_v then (min_v, p'::ps)
        else acc)
      t (v, [p]) in
    match k with
    | 0 => []
    | S k' => min_v :: run_greedy grid k' starts
    end
  end.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[10; 5; 20; 14; 16]; [7; 11; 12; 17; 9]; [13; 19; 1; 15; 8]; [3; 18; 4; 6; 2]; [22; 21; 23; 24; 25]] in
  let k := 25 in
  let output := [1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1; 4; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.