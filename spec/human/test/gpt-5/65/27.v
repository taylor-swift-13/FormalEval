Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Fixpoint z_to_digits_fuel (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if Z.ltb n 10%Z then
        [n]
      else
        (z_to_digits_fuel (Z.div n 10%Z) fuel') ++ [Z.rem n 10%Z]
  end.

Definition z_to_digits (n : Z) : list Z :=
  if Z.eqb n 0%Z then
    [0%Z]
  else
    let n' := Z.abs n in
    let fuel := S (S (Z.to_nat (Z.log2 n'))) in
    z_to_digits_fuel n' fuel.

Definition z_digit_to_string (d : Z) : string :=
  match d with
  | 0%Z => "0" | 1%Z => "1" | 2%Z => "2" | 3%Z => "3" | 4%Z => "4"
  | 5%Z => "5" | 6%Z => "6" | 7%Z => "7" | 8%Z => "8" | 9%Z => "9"
  | _ => ""
  end.

Fixpoint z_from_digits_to_string (l : list Z) : string :=
  match l with
  | [] => ""
  | h :: t => (z_digit_to_string h) ++ (z_from_digits_to_string t)
  end.

Definition circular_shift_impl (x : Z) (shift : Z) : string :=
  let digits := z_to_digits x in
  let len := length digits in
  if Z.eqb x 0%Z then
    "0"
  else
    let lenZ := Z.of_nat len in
    if Z.ltb lenZ shift then
      z_from_digits_to_string (rev digits)
    else
      let effective_shift := Z.rem shift lenZ in
      if Z.eqb effective_shift 0%Z then
        z_from_digits_to_string digits
      else
        let split_point_Z := Z.sub lenZ effective_shift in
        let split_point_nat := Z.to_nat split_point_Z in
        let new_head := skipn split_point_nat digits in
        let new_tail := firstn split_point_nat digits in
        z_from_digits_to_string (new_head ++ new_tail).

Definition problem_65_pre (x : Z) (shift : Z) : Prop := True.

Definition problem_65_spec (x : Z) (shift : Z) (result : string) : Prop :=
  result = circular_shift_impl x shift.

Example problem_65_test_case_Z :
  problem_65_spec 789456124%Z 789456124%Z "421654987".
Proof.
  unfold problem_65_spec.
  vm_compute.
  reflexivity.
Qed.