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

Fixpoint extract_ints (s : string) (curr : Z) (in_num : bool) : list Z :=
  match s with
  | EmptyString => if in_num then [curr] else []
  | String c rest =>
      if is_digit c then
        extract_ints rest (curr * 10 + char_to_Z c) true
      else
        if in_num then curr :: extract_ints rest 0 false
        else extract_ints rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := extract_ints s 0 false in
  n - fold_right Z.add 0 numbers.

Example check_fruit_distribution : fruit_distribution "3 apples and 7 oranges" 25 = 15.
Proof. reflexivity. Qed.