Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint sum_numbers_aux (s : string) (curr : Z) (acc : Z) : Z :=
  match s with
  | EmptyString => acc + curr
  | String c s' =>
      if is_digit c then
        sum_numbers_aux s' (curr * 10 + digit_to_Z c) acc
      else
        sum_numbers_aux s' 0 (acc + curr)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_numbers_aux s 0 0.

Example fruit_distribution_example : fruit_distribution "3 apples and 7 oranges" 20 = 10.
Proof. reflexivity. Qed.