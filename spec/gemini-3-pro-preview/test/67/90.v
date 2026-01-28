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

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers (s : string) (acc : Z) (in_num : bool) : list Z :=
  match s with
  | EmptyString => if in_num then [acc] else []
  | String c rest =>
      if is_digit c then
        extract_numbers rest (acc * 10 + to_digit c) true
      else
        if in_num then acc :: extract_numbers rest 0 false
        else extract_numbers rest 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s 0 false in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "24 apples and 18 oranges" 105 = 63.
Proof. reflexivity. Qed.