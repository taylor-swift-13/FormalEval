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

Fixpoint extract_numbers (s : string) (acc : Z) (reading : bool) : list Z :=
  match s with
  | EmptyString => if reading then [acc] else []
  | String c s' =>
    if is_digit c then
      extract_numbers s' (acc * 10 + to_digit c) true
    else
      if reading then acc :: extract_numbers s' 0 false
      else extract_numbers s' 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s 0 false in
  let sum := fold_left Z.add nums 0 in
  n - sum.

Example fruit_distribution_example_new : fruit_distribution "0 apples and 0 oranges" 0 = 0.
Proof. reflexivity. Qed.