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

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (curr : Z) (building : bool) : list Z :=
  match s with
  | EmptyString => if building then [curr] else []
  | String c rest =>
      if is_digit c then
        let val := char_to_Z c in
        if building then
          parse_numbers rest (curr * 10 + val) true
        else
          parse_numbers rest val true
      else
        if building then
          curr :: parse_numbers rest 0 false
        else
          parse_numbers rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s 0 false in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "3 apples and 4 oranges" 10 = 3.
Proof.
  compute.
  reflexivity.
Qed.