(* Given a list of positive integers x. return a sorted list of all
elements that hasn't any even digit.

Note: Returned list should be sorted in increasing order.

For example:
>>> unique_digits([15, 33, 1422, 1])
[1, 15, 33]
>>> unique_digits([152, 323, 1422, 10])
[] *)



(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.

Import ListNotations.



(* 辅助定义：判断单个数字是否为奇数 (与之前相同) *)
Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.


Fixpoint all_digits_odd_list (l : list nat) : Prop :=
  match l with
  | [] => True (* 空列表满足条件 *)
  | h :: t => is_odd_digit h /\ all_digits_odd_list t (* 头部是奇数且尾部也满足条件 *)
  end.

(*
  将 nat 转换为 list nat (使用结构递归)
*)

(*
  这是一个使用 "fuel" 技巧的辅助函数。
  - n: 我们要转换的数。
  - fuel: 一个计数器，确保递归会终止。递归调用在 fuel 的前驱 (fuel') 上进行。
*)
Fixpoint nat_to_digits_fueled (n fuel : nat) : list nat :=
  match fuel with
  | 0 => [] (* 燃料耗尽，停止 *)
  | S fuel' => (* 还有燃料，继续 *)
      (* 我们也需要检查 n 是否已经为0 *)
      if Nat.eqb n 0 then
        []
      else
        (n mod 10) :: nat_to_digits_fueled (n / 10) fuel'
  end.

(*
  主转换函数。
  它调用辅助函数，并提供足够的 "fuel"。
  一个安全的做法是提供 n 本身作为 fuel，因为一个数字的位数永远不会超过其本身的值。
*)
Definition nat_to_digits (n : nat) : list nat :=
  nat_to_digits_fueled n n.


Definition has_only_odd_digits (n : nat) : Prop :=
  all_digits_odd_list (nat_to_digits n).

(*
  第四部分: 最终的程序规约 (保持不变)
*)

Definition unique_digits_spec (x y : list nat) : Prop :=
  (* 条件1: 过滤和完整性 *)
  (forall n : nat, In n y <-> In n x /\ has_only_odd_digits n) /\

  (* 条件2: 排序 *)
  (Sorted le y).
