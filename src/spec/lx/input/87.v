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

(*
 * get_row 函数的程序规约 (Spec)
 *)
Definition get_row_spec (lst : list (list nat)) (x : nat) (res : list (nat * nat)) : Prop :=
  (* 1. 成员正确性 (Correctness):
        输出列表 res 中的每一个坐标 (r, c) 在输入列表 lst 中都必须对应元素 x。*)
  (forall coord : nat * nat, In coord res -> get_elem lst coord = Some x) /\

  (* 2. 完整性 (Completeness):
        输入列表 lst 中所有值为 x 的元素的坐标 (r, c) 都必须包含在输出列表 res 中。*)
  (forall r c : nat,
    match get_elem lst (r, c) with
    | Some v => v = x -> In (r, c) res
    | None => True
    end) /\

  (* 3. 排序规则 (Sorting):
        输出列表 res 必须是根据 coord_order 规则排序的。*)
  is_sorted res.