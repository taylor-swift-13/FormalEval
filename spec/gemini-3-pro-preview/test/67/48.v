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

Fixpoint parse_numbers_aux (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match acc with
        | Some n => parse_numbers_aux s' (Some (n * 10 + d))
        | None => parse_numbers_aux s' (Some d)
        end
      else
        match acc with
        | Some n => n :: parse_numbers_aux s' None
        | None => parse_numbers_aux s' None
        end
  end.

Definition parse_numbers (s : string) : list Z :=
  parse_numbers_aux s None.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "10 apples and 20 oranges" 52 = 22.
Proof. reflexivity. Qed.