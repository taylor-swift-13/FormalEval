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

Fixpoint parse_sum_aux (s : string) (curr : Z) (acc : Z) : Z :=
  match s with
  | EmptyString => acc + curr
  | String c rest =>
      if is_digit c then
        parse_sum_aux rest (curr * 10 + digit_to_Z c) acc
      else
        parse_sum_aux rest 0 (acc + curr)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_sum_aux s 0 0.

Example test_fruit_distribution : fruit_distribution "0 apples and 0 oranges" 12 = 12.
Proof. reflexivity. Qed.