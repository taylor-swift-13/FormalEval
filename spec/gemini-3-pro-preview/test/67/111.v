Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (n >=? 48) && (n <=? 57).

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint extract_sum (s : string) (current : Z) (is_parsing : bool) (acc : Z) : Z :=
  match s with
  | EmptyString => if is_parsing then acc + current else acc
  | String c s' =>
      if is_digit c then
        extract_sum s' (current * 10 + char_to_Z c) true acc
      else
        if is_parsing then
          extract_sum s' 0 false (acc + current)
        else
          extract_sum s' 0 false acc
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - extract_sum s 0 false 0.

Example fruit_distribution_example : fruit_distribution "97 apples and 1 oranges" 200 = 102.
Proof.
  compute.
  reflexivity.
Qed.