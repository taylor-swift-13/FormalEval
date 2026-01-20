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
  let '(r,c) := p in [(r, c+1); (r+1, c); (r, c-1); (r-1, c)].

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

(* 简单的 DFS 穷举搜索（受限 fuel），选择字典序最小的路径值序列 *)
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

Example find_minimum_path_impl_1x1_typecheck:
  exists l : list nat, l = find_minimum_path_impl ((1%nat::nil)::nil) 1%nat.
Proof. eexists; reflexivity. Qed.

Definition find_minimum_path_spec (grid : Grid) (k : nat) (output : list nat) : Prop :=
  output = find_minimum_path_impl grid k.


