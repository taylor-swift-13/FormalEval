(* def specialFilter(nums):
"""Write a function that takes an array of numbers as input and returns
the number of elements in the array that are greater than 10 and both
first and last digits of a number are odd (1, 3, 5, 7, 9).
For example:
specialFilter([15, -73, 14, -15]) => 1
specialFilter([33, -2, -3, 45, 21, 109]) => 2
""" *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* 定义一个辅助函数来获取一个正数的最后一位数字 *)
Definition last_digit (n : Z) : Z :=
  Z.abs (n mod 10).

(* msd_fuel: 一个带有 "fuel" 的辅助函数
   功能: 获取一个正数的最高位数字 (Most Significant Digit) *)
Fixpoint msd_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O => n mod 10 (* 燃料耗尽，这通常不应该发生 *)
  | S f =>
    if Z_lt_dec n 10 then n (* 如果 n 是个位数, 它就是最高位 *)
    else msd_fuel f (n / 10) (* 否则, 继续除以10寻找最高位 *)
  end.

(* 定义一个返回 bool 的谓词来检查单个数字是否满足所有条件 *)
Definition special_number_b (n : Z) : bool :=
  let abs_n := Z.abs n in
  (* 使用布尔运算符 && 和返回 bool 的函数 *)
  (10 <? n) && (Z.odd (msd_fuel (Z.to_nat abs_n) abs_n)) && (Z.odd (last_digit abs_n)).

(* specialFilter 程序的规约 *)
Definition specialFilter_spec (nums : list Z) (output : Z) : Prop :=
  output = Z.of_nat (length (filter special_number_b nums)).