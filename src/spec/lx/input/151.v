(* def double_the_difference(lst):
'''
Given a list of numbers, return the sum of squares of the numbers
in the list that are odd. Ignore numbers that are negative or not integers.

double_the_difference([1, 3, 2, 0]) == 1 + 9 + 0 + 0 = 10
double_the_difference([-1, -2, 0]) == 0
double_the_difference([9, -2]) == 81
double_the_difference([0]) == 0

If the input list is empty, return 0. *)
(* 引入所需的库 *)
Require Import ZArith. (* 用于整数操作 *)
Require Import List.   (* 用于列表操作 *)
Require Import Bool.   (* 用于布尔操作, 比如 && *)
Import ListNotations.
Open Scope bool_scope. (* 打开布尔作用域以使用 && 符号 *)

(*
  sum_sq_odd 是一个辅助的计算函数，它递归地处理列表：
  - 如果列表为空，结果为 0。
  - 如果列表的头部元素 h 是一个非负奇数，则将其平方加入到剩余列表的计算结果中。
  - 否则，忽略当前元素，继续处理剩余的列表。
*)
Fixpoint sum_sq_odd (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t =>
    if (Z.leb 0 h) && (Z.odd h)
    then h * h + sum_sq_odd t
    else sum_sq_odd t
  end.

(*
  double_the_difference_spec 是程序的规约 (Spec)。
  它是一个一阶逻辑断言，描述了输入 l (一个整数列表) 和输出 res (一个整数) 之间的关系。
  这个关系是：res 必须等于对输入列表 l 调用 sum_sq_odd 函数的结果。
*)
Definition double_the_difference_spec (l : list Z) (res : Z) : Prop :=
  res = sum_sq_odd l.