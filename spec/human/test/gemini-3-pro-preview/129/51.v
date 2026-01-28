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

Fixpoint lex_le (l1 l2 : list nat) : bool :=
  match l1,l2 with
  | [], _ => true
  | _::_, [] => false
  | h1::t1, h2::t2 => (h1 <? h2) || (andb (h1 =? h2) (lex_le t1 t2))
  end.

Definition get_path_values (grid:Grid) (path:list Pos) : list nat := map (get_val grid) (rev path).

Fixpoint best_path_by_lex (grid:Grid) (candidates:list (list Pos)) : list Pos :=
  match candidates with
  | [] => []
  | p::ps =>
    match ps with
    | [] => p
    | _ =>
      let best_rest := best_path_by_lex grid ps in
      let v_p := get_path_values grid p in
      let v_best := get_path_values grid best_rest in
      if lex_le v_p v_best then p else best_rest
    end
  end.

Fixpoint generate_cols (r:nat) (c:nat) (w:nat) : list Pos :=
  match w with
  | 0 => []
  | S w' => (r, c) :: generate_cols r (S c) w'
  end.

Fixpoint generate_coords (r:nat) (h:nat) (w:nat) : list Pos :=
  match h with
  | 0 => []
  | S h' => generate_cols r 0 w ++ generate_coords (S r) h' w
  end.

Definition prune_paths (grid:Grid) (paths:list (list Pos)) : list (list Pos) :=
  let h := length grid in
  let w := match grid with [] => 0 | r::_ => length r end in
  let coords := generate_coords 0 h w in
  fold_right (fun pos acc =>
    let starting_at_pos := filter (fun p => match p with q::_ => andb (fst q =? fst pos) (snd q =? snd pos) | [] => false end) paths in
    match starting_at_pos with
    | [] => acc
    | _ => best_path_by_lex grid starting_at_pos :: acc
    end
  ) [] coords.

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
    let pruned := prune_paths grid ex in
    extend_paths grid (k-1) f' pruned
  end.

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
  let cand := extend_paths grid k (k * (length grid + 1)) starts in
  best_by_lex grid cand.

Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Example test_case_proof :
  let grid := [[1; 2; 3; 4; 5]; [6; 7; 8; 9; 10]; [11; 12; 13; 14; 15]; [16; 17; 18; 19; 20]; [21; 22; 23; 24; 25]] in
  let k := 20 in
  let output := [1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2; 1; 2] in
  problem_129_spec grid k output.
Proof.
  unfold problem_129_spec.
  unfold find_minimum_path_impl.
  vm_compute.
  reflexivity.
Qed.