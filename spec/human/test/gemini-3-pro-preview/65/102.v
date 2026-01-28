Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* Provided Definitions *)

Fixpoint to_digits_fuel (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10) then
        [n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [n mod 10]
  end.

Definition to_digits (n : Z) : list Z :=
  if (n =? 0) then
    [0]
  else
    to_digits_fuel n 100%nat.

Definition digit_to_string (d : Z) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list Z) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : Z) (shift : Z) : string :=
  let digits := to_digits x in
  let len := Z.of_nat (length digits) in
  if (x =? 0) then
    "0"
  else
    if (len <? shift) then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len in
      if (effective_shift =? 0) then
        from_digits_to_string digits
      else
        let split_point := Z.to_nat (len - effective_shift) in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : Z) (shift : Z) : Prop := True.

Definition problem_65_spec (x : Z) (shift : Z) (result : string) : Prop :=
  result = circular_shift_impl x shift.

(* Test Case Proof *)

Example test_circular_shift_large : problem_65_spec 1234567890987654321 158 "1234567890987654321".
Proof.
  unfold problem_65_spec.
  unfold circular_shift_impl.
  vm_compute.
  reflexivity.
Qed.