(*def skjkasdkd(lst):
"""You are given a list of integers.
You need to find the largest prime value and return the sum of its digits.

Examples:
For lst = [0,3,2,1,3,5,7,4,5,5,5,2,181,32,4,32,3,2,32,324,4,3] the output should be 10
For lst = [1,0,1,8,2,4597,2,1,3,40,1,2,1,2,4,2,5,1] the output should be 25
For lst = [1,3,1,32,5107,34,83278,109,163,23,2323,32,30,1,9,3] the output should be 13
For lst = [0,724,32,71,99,32,6,0,5,91,83,0,5,6] the output should be 11
For lst = [0,81,12,3,1,21] the output should be 3
For lst = [0,8,1,2,1,7] the output should be 7
""" *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* 辅助定义1: 判断一个数是否为素数 *)
Definition IsPrime (n : nat) : Prop :=
  n > 1 /\ (forall d : nat, d mod n = 0 -> d = 1 \/ d = n).

(*
  辅助定义2: 计算一个自然数各位数字之和 (使用燃料)

  sum_digits_fueled 是一个辅助函数，它接受一个额外的 fuel 参数。
  递归在 fuel 上进行，Coq 可以验证它是结构递减的。
*)
Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* 燃料耗尽，停止递归 *)
  | S fuel' =>
    match n with
    | 0 => 0 (* n 本身为 0，则各位和为 0 *)
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

(*
  最终的 sum_digits 函数。
  我们为它提供 n 作为初始燃料，这总是足够用的，
  因为一个数的位数总是小于或等于其本身。
*)
Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

(*
  程序规约 Spec 的定义
  (这部分与之前相同，但现在依赖于修正后的 sum_digits)
*)
Definition Spec (lst : list nat) (output : nat) : Prop :=
  exists p,
    (* 1. 必须存在一个p，它是列表lst中的元素 *)
    In p lst /\

    (* 2. p必须是一个素数 *)
    IsPrime p /\

    (* 3. p是列表lst中所有素数里最大的一个 *)
    (forall p', In p' lst -> IsPrime p' -> p' <= p) /\

    (* 4. 最终的输出output等于p的各位数字之和 *)
    output = sum_digits p.