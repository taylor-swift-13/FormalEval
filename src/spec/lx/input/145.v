(* def order_by_points(nums):
"""
Write a function which sorts the given list of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original list.

For example:
>>> order_by_points([1, 11, -1, -11, -12]) == [-1, -11, 1, -12, 11]
>>> order_by_points([]) == []
""" *)
(* 导入所需库 *)
Require Import ZArith.
Require Import Coq.Lists.List.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import Arith.
Import ListNotations.
Open Scope Z_scope.

(* -------- 用户提供的函数 -------- *)
(*
  sum_digits_pos_fuel: 一个带有 "fuel" 的辅助函数
  功能: 计算一个正整数的各位数之和
*)
Fixpoint sum_digits_pos_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => 0 (* 燃料耗尽，返回 0 *)
  | S f => (* 还有燃料 *)
      if Z_le_gt_dec n 0 then 0 (* 如果 n <= 0, 递归结束 *)
      else (n mod 10) + sum_digits_pos_fuel f (n / 10)
        (* 加上个位数，然后对 n/10 进行递归调用，并消耗一个 fuel *)
  end.

(*
  msd_fuel: 一个带有 "fuel" 的辅助函数
  功能: 获取一个正整数的最高位数字 (Most Significant Digit)
*)
Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10 (* 燃料耗尽，返回个位数 *)
  | S f => (* 还有燃料 *)
      if Z_lt_le_dec n 10 then n (* 如果 n 是个位数，它就是最高位 *)
      else msd_fuel f (n / 10) (* 否则，继续除以10寻找最高位 *)
  end.

(*
  sum_digits: 主函数
  功能: 计算整数的各位数之和
*)
Definition sum_digits (n : Z) : Z :=
  if Z_ge_dec n 0 then
    (* 情况1: n 是非负数 *)
    sum_digits_pos_fuel (Z.to_nat n + 1) n
  else
    (* 情况2: n 是负数 *)
    let n_pos := -n in (* 取 n 的绝对值 *)
    let total_sum := sum_digits_pos_fuel (Z.to_nat n_pos + 1) n_pos in
    let first_digit := msd_fuel (Z.to_nat n_pos + 1) n_pos in
    total_sum - 2 * first_digit.

(* -------- 程序规约 (Specification) -------- *)

(*
 * @brief 定义两个带有原始索引的整数之间的“小于或等于”关系。
 * @param p1, p2 : (整数, 原始索引) 对。
 * 排序规则:
 * 1. 首先根据各位数之和 (sum_digits) 升序排列。
 * 2. 如果和相等, 则根据原始索引 (idx) 升序排列。
 *)
Definition le_stable (p1 p2 : Z * nat) : Prop :=
  let (z1, idx1) := p1 in
  let (z2, idx2) := p2 in
  let s1 := sum_digits z1 in
  let s2 := sum_digits z2 in
  s1 < s2 \/ (s1 = s2 /\ (idx1 <= idx2)%nat).


(*
 * @brief order_by_points 函数的程序规约。
 * @param l_in 输入的整数列表。
 * @param l_out 输出的整数列表。
 *)
Definition order_by_points_spec (l_in l_out : list Z) : Prop :=
  (* 将输入列表与它的索引配对，例如 [a, b, c] -> [(a,0), (b,1), (c,2)] *)
  let l_in_indexed := combine l_in (seq 0 (length l_in)) in
  (* 规约要求存在一个中间的、带索引的列表 l_out_indexed *)
  exists (l_out_indexed : list (Z * nat)),
    (* 1. l_out_indexed 必须是 l_in_indexed 的一个排列，
          这保证了元素的完整性（没有丢失或增加）。 *)
    Permutation l_in_indexed l_out_indexed /\
    (* 2. l_out_indexed 必须根据 le_stable 关系是排序好的。 *)
    Sorted le_stable l_out_indexed /\
    (* 3. 最终的输出列表 l_out 是 l_out_indexed 去掉索引后的结果。 *)
    l_out = map fst l_out_indexed.