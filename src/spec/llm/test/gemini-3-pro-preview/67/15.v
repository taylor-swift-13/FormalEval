Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (acc : Z) (in_num : bool) : list Z :=
  match s with
  | EmptyString => if in_num then [acc] else []
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        if in_num then parse_numbers s' (acc * 10 + d) true
        else parse_numbers s' d true
      else
        if in_num then acc :: parse_numbers s' 0 false
        else parse_numbers s' 0 false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s 0 false in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "3 apples and 5 oranges" 12 = 4.
Proof. reflexivity. Qed.