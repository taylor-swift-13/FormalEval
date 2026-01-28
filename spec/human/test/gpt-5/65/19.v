Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

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

Fixpoint to_digits_Z_fuel (n : Z) (fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.leb n 9%Z then
        [Z.to_nat n]
      else
        (to_digits_Z_fuel (Z.div n 10%Z) fuel') ++ [Z.to_nat (Z.modulo n 10%Z)]
  end.

Definition to_digits_Z (n : Z) : list nat :=
  if Z.eqb n 0%Z then
    [0]
  else
    to_digits_Z_fuel n 100%nat.

Definition circular_shift_impl_Z (x : Z) (shift : Z) : string :=
  let digits := to_digits_Z x in
  let len := length digits in
  if Z.eqb x 0%Z then
    "0"
  else
    let shift_nat := Z.to_nat shift in
    if (len <? shift_nat)%nat then
      from_digits_to_string (rev digits)
    else
      let effective_shift := Nat.modulo shift_nat len in
      if (effective_shift =? 0)%nat then
        from_digits_to_string digits
      else
        let split_point := len - effective_shift in
        let new_head := skipn split_point digits in
        let new_tail := firstn split_point digits in
        from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : Z) (shift : Z) : Prop := True.

Definition problem_65_spec (x : Z) (shift : Z) (result : string) : Prop :=
  result = circular_shift_impl_Z x shift.

Example problem_65_test_case_Z :
  problem_65_spec 789456123%Z 23%Z "321654987".
Proof.
  unfold problem_65_spec.
  vm_compute.
  reflexivity.
Qed.