(* def circular_shift(x, shift):
"""Circular shift the digits of the integer x, shift the digits right by shift
and return the result as a string.
If shift > number of digits, return digits reversed.
>>> circular_shift(12, 1)
"21"
>>> circular_shift(12, 2)
"12"
""" *)
(* 导入所需的标准库 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.


Open Scope string_scope.

(* ================================================================= *)
(* 1. 实现 to_digits                         *)
(* ================================================================= *)

Fixpoint to_digits_fuel (n fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10)%nat then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : nat) : list nat :=
  if (n =? 0)%nat then
    [0]
  else
    to_digits_fuel n n.

(* 示例： *)
(* Eval compute in (to_digits 123).  (* 得到 [1; 2; 3] *) *)
(* Eval compute in (to_digits 0).    (* 得到 [0] *) *)


(* ================================================================= *)
(* 2. 实现 from_digits_to_string            *)
(* ================================================================= *)

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

(* ================================================================= *)
(* 3. 最终的程序规约 (Spec)              *)
(* ================================================================= *)

Definition circular_shift_spec (x : nat) (shift : nat) (result : string) : Prop :=
  let digits := to_digits x in
  let len := length digits in
  (x = 0 /\ result = "0")
  \/
  (x > 0 /\ (
    (len < shift /\ result = from_digits_to_string (rev digits))
    \/
    (shift <= len /\
      let effective_shift := shift mod len in
      if (effective_shift =? 0)%nat then
        result = from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        result = from_digits_to_string (new_head ++ new_tail))
  )).