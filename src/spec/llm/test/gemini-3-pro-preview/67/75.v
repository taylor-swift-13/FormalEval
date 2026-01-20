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

Fixpoint extract_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c rest =>
      if is_digit c then
        match acc with
        | Some n => extract_numbers rest (Some (n * 10 + digit_to_Z c))
        | None => extract_numbers rest (Some (digit_to_Z c))
        end
      else
        match acc with
        | Some n => n :: extract_numbers rest None
        | None => extract_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution : fruit_distribution "3 apples and 7 oranges" 15 = 5.
Proof.
  reflexivity.
Qed.