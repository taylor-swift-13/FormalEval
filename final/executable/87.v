(* def get_row(lst, x):
"""
You are given a 2 dimensional data, as a nested lists,
which is similar to matrix, however, unlike matrices,
each row may contain a different number of columns.
Given lst, and integer x, find integers x in the list,
and return list of tuples, [(x1, y1), (x2, y2) ...] such that
each tuple is a coordinate - (row, columns), starting with 0.
Sort coordinates initially by rows in ascending order.
Also, sort coordinates of the row by columns in descending order.

Examples:
get_row([
[1,2,3,4,5,6],
[1,2,3,4,1,6],
[1,2,3,4,5,1]
], 1) == [(0, 0), (1, 4), (1, 0), (2, 5), (2, 0)]
get_row([], 1) == []
get_row([[], [1], [1, 2, 3]], 3) == [(2, 2)]
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(*
 * 辅助定义：根据坐标 (r, c) 从嵌套列表中获取元素。
 * 如果坐标无效，则返回 None。
 *)
Definition get_elem {A : Type} (lst : list (list A)) (coord : nat * nat) : option A :=
  match nth_error lst (fst coord) with
  | Some row => nth_error row (snd coord)
  | None => None
  end.

(*
 * 排序关系定义：
 * - 首先按行号 (r) 升序。
 * - 如果行号相同，则按列号 (c) 降序。
 *)
Inductive coord_order (c1 c2 : nat * nat) : Prop :=
  | row_lt : fst c1 < fst c2 -> coord_order c1 c2
  | col_gt : fst c1 = fst c2 -> snd c1 > snd c2 -> coord_order c1 c2.

(*
 * 修正后的 is_sorted 定义：
 * 检查一个坐标列表是否根据 coord_order 关系进行了排序。
 * 这个版本可以通过 Coq 的终止性检查。
 *)
Fixpoint is_sorted (l : list (nat * nat)) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | c1 :: (c2 :: _ as tail) => coord_order c1 c2 /\ is_sorted tail
  end.

Fixpoint collect_coords_row (row : list nat) (r c : nat) (x : nat) : list (nat * nat) :=
  match row with
  | [] => []
  | h :: t =>
      if Nat.eqb h x then
        (r, c) :: collect_coords_row t r (S c) x
      else
        collect_coords_row t r (S c) x
  end.

Fixpoint collect_all_coords (lst : list (list nat)) (r : nat) (x : nat) : list (nat * nat) :=
  match lst with
  | [] => []
  | row :: rest =>
      collect_coords_row row r 0 x ++ collect_all_coords rest (S r) x
  end.

Fixpoint insert_coord (coord : nat * nat) (coords : list (nat * nat)) : list (nat * nat) :=
  match coords with
  | [] => [coord]
  | h :: t =>
      if Nat.ltb (fst coord) (fst h) then
        coord :: coords
      else if Nat.eqb (fst coord) (fst h) then
        if Nat.ltb (snd h) (snd coord) then
          coord :: coords
        else
          h :: insert_coord coord t
      else
        h :: insert_coord coord t
  end.

Fixpoint sort_coords (coords : list (nat * nat)) : list (nat * nat) :=
  match coords with
  | [] => []
  | h :: t => insert_coord h (sort_coords t)
  end.

Definition get_row_impl (lst : list (list nat)) (x : nat) : list (nat * nat) :=
  sort_coords (collect_all_coords lst 0 x).

Definition get_row_spec (lst : list (list nat)) (x : nat) (res : list (nat * nat)) : Prop :=
  res = get_row_impl lst x.