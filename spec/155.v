(* def even_odd_count(num):
"""Given an integer. return a tuple that has the number of even and odd digits respectively.

Example:
even_odd_count(-12) ==> (1, 1)
even_odd_count(123) ==> (1, 2)
""" *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* 定义一个辅助函数来计算一个数字列表的偶数和奇数个数 *)
Fixpoint count_digits_acc (l : list Z) (acc : Z * Z) : Z * Z :=
  match l with
  | nil => acc
  | h :: t =>
    let '(even_count, odd_count) := acc in
    if Z.even h then
      count_digits_acc t (even_count + 1, odd_count)
    else
      count_digits_acc t (even_count, odd_count + 1)
  end.

(* 定义一个辅助函数，使用 "fuel" 技巧将整数转换为数字列表 *)
Fixpoint to_digits_fuel (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f' =>
    if n =? 0 then
      nil
    else
      (Z.abs (n mod 10)) :: to_digits_fuel f' (n / 10)
  end.

(*
  Spec even_odd_count_spec (num : Z) (output : Z * Z) : Prop :=
  output = count_digits_acc (to_digits_fuel (Z.to_nat (Z.abs num) + 1) num) (0, 0).
*)

Definition even_odd_count_spec (num : Z) (output : Z * Z) : Prop :=
  let digits := to_digits_fuel (Z.to_nat (Z.abs num) + 1) num in
  let '(even_c, odd_c) := count_digits_acc digits (0, 0) in
  output = (even_c, odd_c).