Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n)%nat && (n <=? 57)%nat).

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c) - 48.

Fixpoint parse_sum (s : string) (current_num : Z) (acc : Z) (in_number : bool) : Z :=
  match s with
  | EmptyString =>
      if in_number then acc + current_num else acc
  | String c rest =>
      if is_digit c then
        parse_sum rest (current_num * 10 + char_to_Z c) acc true
      else
        if in_number then
          parse_sum rest 0 (acc + current_num) false
        else
          parse_sum rest 0 acc false
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - parse_sum s 0 0 false.

Example fruit_distribution_example:
  fruit_distribution "0 apples and 0 oranges" 15 = 15.
Proof.
  compute.
  reflexivity.
Qed.