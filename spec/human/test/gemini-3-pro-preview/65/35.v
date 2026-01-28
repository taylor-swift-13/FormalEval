Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* Provided Definitions *)

Fixpoint to_digits_fuel (n : Z) (fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if (n <? 10) then
        [Z.to_nat n]
      else
        (to_digits_fuel (n / 10) fuel') ++ [Z.to_nat (n mod 10)]
  end.

Definition to_digits (n : Z) : list nat :=
  if (n =? 0) then
    [0%nat]
  else
    to_digits_fuel n 100%nat.

Definition digit_to_string (d : nat) : string :=
  match d with
  | 0%nat => "0" | 1%nat => "1" | 2%nat => "2" | 3%nat => "3" | 4%nat => "4"
  | 5%nat => "5" | 6%nat => "6" | 7%nat => "7" | 8%nat => "8" | 9%nat => "9"
  | _ => ""
  end.

Fixpoint from_digits_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | h :: t => (digit_to_string h) ++ (from_digits_to_string t)
  end.

Definition circular_shift_impl (x : Z) (shift : Z) : string :=
  let digits := to_digits x in
  let len := length digits in
  let len_Z := Z.of_nat len in
  if (x =? 0) then
    "0"
  else
    if (len_Z <? shift) then
      from_digits_to_string (rev digits)
    else
      let effective_shift := shift mod len_Z in
      if (effective_shift =? 0) then
        from_digits_to_string digits
      else
        let split_point := Z.to_nat (len_Z - effective_shift) in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : Z) (shift : Z) : Prop := True.

Definition problem_65_spec (x : Z) (shift : Z) (result : string) : Prop :=
  result = circular_shift_impl x shift.

(* Test Case Proof *)

Example test_circular_shift_789456124_3 : problem_65_spec 789456124 3 "124789456".
Proof.
  unfold problem_65_spec.
  unfold circular_shift_impl.
  vm_compute.
  reflexivity.
Qed.