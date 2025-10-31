(* def digits(n):
"""Given a positive integer n, return the product of the odd digits.
Return 0 if all digits are even.
For example:
digits(1) == 1
digits(4) == 0
digits(235) == 15
"""*)
(* 导入所需的库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(*
  一个带有 "fuel" 参数的辅助函数，用于确保终止。
  这个函数在 fuel 上是结构递归的。
*)
Fixpoint get_digits_helper (n : nat) (fuel : nat) : list nat :=
  match fuel with
  | 0 => [] (* 燃料耗尽，停止 *)
  | S fuel' => (* 还有燃料，继续计算 *)
      match n with
      | 0 => [] (* n 已经是 0，停止 *)
      | _ => (Nat.modulo n 10) :: get_digits_helper (Nat.div n 10) fuel'
      end
  end.

(*
  获取数字列表的主函数。
  它调用辅助函数并提供 n 作为初始燃料，这足以完成计算。
*)
Definition get_digits (n : nat) : list nat :=
  get_digits_helper n n.

(*
  计算一个数字列表乘积的函数。
  这部分和之前一样。
*)
Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

(*
  `digits` 函数的程序规约。
  这部分的逻辑和之前完全一样，只是它现在依赖于我们新定义的 get_digits。
*)
Definition digits_spec (n : nat) (z : nat) : Prop :=
  (* 1. 获取 n 的所有数字 *)
  let all_digits := get_digits n in
  (* 2. 筛选出所有奇数数字 *)
  let odd_digits := filter Nat.odd all_digits in
  (* 3. 根据是否存在奇数数字来定义输入和输出的关系 *)
  match odd_digits with
  | [] => z = 0 (* 如果没有奇数数字，结果必须是 0 *)
  | _ => z = product odd_digits (* 否则，结果是奇数数字的乘积 *)
  end.