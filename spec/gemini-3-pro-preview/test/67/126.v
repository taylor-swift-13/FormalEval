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

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString => 
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        match acc with
        | Some n => parse_numbers s' (Some (n * 10 + digit_to_Z c))
        | None => parse_numbers s' (Some (digit_to_Z c))
        end
      else
        match acc with
        | Some n => n :: parse_numbers s' None
        | None => parse_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_numbers s None in
  n - fold_right Z.add 0 nums.

Example fruit_distribution_test : fruit_distribution "20 apples and 0 oranges" 200 = 180.
Proof.
  reflexivity.
Qed.