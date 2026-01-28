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

Definition get_last_val (grid:Grid) (path:list Pos) : nat :=
  match path with
  | [] => 0
  | u::_ => get_val grid u
  end.

Definition filter_best (grid:Grid) (paths:list (list Pos)) : list (list Pos) :=
  match paths with
  | [] => []
  | p::ps =>
    let val_p := get_last_val grid p in
    let (best, _) := 
      fold_left (fun acc q =>
        let '(b, m) := acc in
        let v := get_last_val grid q in
        if v <? m then ([q], v)
        else if v =? m then (q::b, m)
        else (b, m)) ps ([p], val_p) in
    best
  end.

Fixpoint extend_greedy (grid:Grid) (k:nat) (paths:list (list Pos)) : list (list Pos) :=
  match k with
  | 0 | 1 => paths
  | S k' =>
    let ex :=
      flat_map (fun p =>
        match p with
        | [] => []
        | u::_ => 
          let nbs := filter (in_bounds grid) (neighbors u) in
          map (fun nb => nb::p) nbs
        end) paths in
    let best_ex := filter_best grid ex in
    extend_greedy grid k' best_ex
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
  let starts := build_starts grid 0 in
  let best_starts := filter_best grid starts in
  let cand := extend_greedy grid k best_starts in
  best_by_lex grid cand.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 3; 5; 7]; [9; 11; 13; 15]; [2; 4; 6; 8]; [10; 12; 14; 16]] in
  let k := 15 in
  let output := [1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1; 3; 1] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.