Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := Z.of_nat (nat_of_ascii c) in
  (48 <=? n) && (n <=? 57).

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_and_sum (s : string) (curr : Z) (acc : Z) : Z :=
  match s with
  | EmptyString => acc + curr
  | String c s' =>
      if is_digit c then
        parse_and_sum s' (curr * 10 + digit_to_Z c) acc
      else
        parse_and_sum s' 0 (acc + curr)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_and_sum s 0 0.

Example test_fruit_distribution: fruit_distribution "8 apples and 2 oranges" 10 = 0.
Proof.
  reflexivity.
Qed.