(* def monotonic(l: list):
Return True is list elements are monotonically increasing or decreasing.
>>> monotonic([1, 2, 4, 20])
True
>>> monotonic([1, 20, 4, 10])
False
>>> monotonic([4, 1, 0, -10])
True
*)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(*
 * 谓词：列表 l 是单调递增的。
 * - 空列表或单元素列表是递增的。
 * - 如果 x <= y 并且 (y::l) 是递增的，那么 (x::y::l) 也是递增的。
 *)
Inductive is_increasing : list Z -> Prop :=
| inc_nil: is_increasing []
| inc_single: forall x, is_increasing [x]
| inc_cons: forall x y l, Z.le x y -> is_increasing (y :: l) -> is_increasing (x :: y :: l).

(*
 * 谓词：列表 l 是单调递减的。
 * - 定义方式与 is_increasing 类似。
 *)
Inductive is_decreasing : list Z -> Prop :=
| dec_nil: is_decreasing []
| dec_single: forall x, is_decreasing [x]
| dec_cons: forall x y l, Z.le y x -> is_decreasing (y :: l) -> is_decreasing (x :: y :: l).

(*
 * monotonic 函数的最终程序规约。
 * 输入列表 l 和输出布尔值 b，它们之间的关系是：
 * b 为 true 当且仅当 l 是单调递增或单调递减的。
 *)
(* Pre: no special constraints for `monotonic` on integer lists *)
Definition Pre (l: list Z) : Prop := True.

Definition monotonic_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (is_increasing l \/ is_decreasing l).