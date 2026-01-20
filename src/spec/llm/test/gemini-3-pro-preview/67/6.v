Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers (s : string) (current_num : Z) (in_number : bool) : list Z :=
  match s with
  | EmptyString =>
      if in_number then [current_num] else []
  | String c rest =>
      if is_digit c then
        extract_numbers rest (current_num * 10 + digit_to_Z c) true
      else
        if in_number then
          current_num :: extract_numbers rest 0 false
        else
          extract_numbers rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := extract_numbers s 0 false in
  let sum_fruits := fold_right Z.add 0 numbers in
  n - sum_fruits.

Example fruit_distribution_example : fruit_distribution "2 apples and 3 oranges" 5 = 0.
Proof. reflexivity. Qed.