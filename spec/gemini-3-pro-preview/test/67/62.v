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

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_ints_aux (s : string) (cur : option Z) : list Z :=
  match s with
  | EmptyString =>
      match cur with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match cur with
        | Some n => parse_ints_aux s' (Some (n * 10 + d))
        | None => parse_ints_aux s' (Some d)
        end
      else
        match cur with
        | Some n => n :: parse_ints_aux s' None
        | None => parse_ints_aux s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_ints_aux s None in
  let sum_fruits := fold_right Z.add 0 nums in
  n - sum_fruits.

Example test_fruit_distribution: fruit_distribution "2 apples and 0 oranges" 8 = 6.
Proof. reflexivity. Qed.