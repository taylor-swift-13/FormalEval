(* Write a function count_nums which takes an array of integers and returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, and 3.
>>> count_nums([]) == 0
>>> count_nums([-1, 11, -11]) == 1
>>> count_nums([1, 1, 2]) == 3 *)

(* 引入必要的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Import ListNotations.


(*
  为了让Coq接受在nat上的递归，我们使用一个“fuel”参数，
  递归是针对这个参数进行的，这样就满足了结构递减的要求。
*)

(* 计算自然数各位数之和的辅助函数 *)
Fixpoint nat_sum_digits_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => 0 (* Out of fuel, a safe default *)
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + nat_sum_digits_aux (n / 10) fuel'
    end
  end.

(* 计算自然数最高位数字的辅助函数 *)
Fixpoint nat_get_msd_aux (n : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => n (* Out of fuel, return current n *)
  | S fuel' =>
    if (n <? 10)%nat then n
    else nat_get_msd_aux (n / 10) fuel'
  end.

(*
  主函数调用辅助函数，并提供足够的fuel（n本身就足够了）。
*)
Definition nat_sum_digits (n : nat) : nat :=
  nat_sum_digits_aux n n.

Definition nat_get_msd (n : nat) : nat :=
  nat_get_msd_aux n n.

(*
  根据规则计算整数 'Z' 的“带符号位数之和”。
*)
Definition sum_digits (n : Z) : Z :=
  if Z_gt_dec n 0 then
    Z.of_nat (nat_sum_digits (Z.to_nat n))
  else if Z.eq_dec n 0 then
    0
  else (* n < 0 *)
    let p_nat := Z.to_nat (-n) in
    let total_sum := Z.of_nat (nat_sum_digits p_nat) in
    let msd := Z.of_nat (nat_get_msd p_nat) in
    total_sum - 2 * msd.

(*
  count_nums 函数的最终程序规约 (Spec)。
*)
Definition count_nums_spec (l : list Z) (count : nat) : Prop :=
  count = length (filter (fun z => Z.gtb (sum_digits z) 0) l).