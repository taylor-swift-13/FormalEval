Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith Coq.micromega.Lia.
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
  let base := [(r, S c); (S r, c)] in
  let left := match c with 0 => [] | S c' => [(r, c')] end in
  let up := match r with 0 => [] | S r' => [(r', c)] end in
  base ++ left ++ up.

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

Fixpoint best_by_lex (grid:Grid) (candidates:list (list Pos)) : list nat :=
  match candidates with
  | [] => []
  | [p] => get_path_values grid p
  | p::ps =>
    let v := get_path_values grid p in
    let best_rest := best_by_lex grid ps in
    if lex_le v best_rest then v else best_rest
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

(* k 至少为 1；网格非空且每行非空 *)
Definition problem_129_pre (grid : Grid) (k : nat) : Prop :=
  k >= 1 /\ grid <> [] /\ Forall (fun row => row <> []) grid.

Definition problem_129_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.

Definition grid1 : Grid := [[1;2;3]; [4;5;6]; [7;8;9]].
Definition k1 : nat := 3.
Definition out1 : list nat := [1;2;1].

Example test_case_1_value :
  find_minimum_path_impl grid1 k1 = out1.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example test_case_1_spec :
  problem_129_spec grid1 k1 out1.
Proof.
  unfold problem_129_spec.
  rewrite test_case_1_value.
  reflexivity.
Qed.

Example test_case_1_pre :
  problem_129_pre grid1 k1.
Proof.
  unfold problem_129_pre.
  split.
  - lia.
  - split.
    + discriminate.
    + repeat (constructor; [discriminate|]).
      constructor.
Qed.

Local Open Scope Z_scope.

Definition grid1Z : list (list Z) := [[1%Z;2%Z;3%Z]; [4%Z;5%Z;6%Z]; [7%Z;8%Z;9%Z]].
Definition k1Z : Z := 3%Z.
Definition out1Z : list Z := [1%Z;2%Z;1%Z].

Example test_case_1_Z_value :
  map Z.of_nat (find_minimum_path_impl (map (map Z.to_nat) grid1Z) (Z.to_nat k1Z)) = out1Z.
Proof.
  vm_compute.
  reflexivity.
Qed.