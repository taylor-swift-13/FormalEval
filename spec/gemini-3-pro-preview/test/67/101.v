Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (acc : Z) (in_num : bool) : list Z :=
  match s with
  | EmptyString => if in_num then [acc] else []
  | String c s' =>
      if is_digit c then
        parse_numbers s' (acc * 10 + char_to_Z c) true
      else
        if in_num then acc :: parse_numbers s' 0 false
        else parse_numbers s' 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s 0 false in
  n - fold_right Z.add 0 nums.

Example example_fruit_distribution : fruit_distribution "20 apples and 0 oranges" 197 = 177.
Proof.
  reflexivity.
Qed.