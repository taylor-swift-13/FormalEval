Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_and_sum (s : string) (curr : Z) (in_num : bool) : Z :=
  match s with
  | EmptyString => if in_num then curr else 0
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        parse_and_sum s' (if in_num then curr * 10 + d else d) true
      else
        (if in_num then curr else 0) + parse_and_sum s' 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_and_sum s 0 false.

Example test_fruit_distribution : fruit_distribution "3 apples and 7 oranges" 103%Z = 93%Z.
Proof.
  compute.
  reflexivity.
Qed.