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

Fixpoint parse_and_sum (s : string) (curr : Z) (in_num : bool) (total : Z) : Z :=
  match s with
  | EmptyString => if in_num then total + curr else total
  | String c s' =>
      if is_digit c then
        parse_and_sum s' (curr * 10 + digit_to_Z c) true total
      else
        if in_num then
          parse_and_sum s' 0 false (total + curr)
        else
          parse_and_sum s' 0 false total
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_and_sum s 0 false 0.

Example test_fruit_distribution:
  fruit_distribution "3 apples and 5 oranges" 51 = 43.
Proof.
  reflexivity.
Qed.