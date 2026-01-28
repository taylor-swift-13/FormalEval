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

Definition digit_val (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (curr : Z) (reading : bool) : list Z :=
  match s with
  | EmptyString => if reading then [curr] else []
  | String c rest =>
      if is_digit c then
        parse_numbers rest (curr * 10 + digit_val c) true
      else
        if reading then curr :: parse_numbers rest 0 false
        else parse_numbers rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s 0 false in
  n - fold_right Z.add 0 nums.

Example fruit_distribution_example : fruit_distribution "0 apples and 1 oranges" 15 = 14.
Proof. reflexivity. Qed.