Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition is_digit (a : ascii) : bool :=
  let n := nat_of_ascii a in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (a : ascii) : Z :=
  Z.of_nat (nat_of_ascii a) - 48.

Fixpoint parse_and_sum (s : string) (current_num : Z) (is_parsing : bool) (acc : Z) : Z :=
  match s with
  | EmptyString => if is_parsing then acc + current_num else acc
  | String c s' =>
      if is_digit c then
        parse_and_sum s' (current_num * 10 + digit_to_Z c) true acc
      else
        if is_parsing then
          parse_and_sum s' 0 false (acc + current_num)
        else
          parse_and_sum s' 0 false acc
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_and_sum s 0 false 0.

Example fruit_distribution_example : fruit_distribution "2 apples and 0 oranges" 14 = 12.
Proof. reflexivity. Qed.