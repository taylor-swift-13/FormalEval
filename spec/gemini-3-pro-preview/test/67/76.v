Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers (s : string) (curr : option Z) : list Z :=
  match s with
  | EmptyString => 
      match curr with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := digit_to_Z c in
        match curr with
        | Some n => extract_numbers s' (Some (n * 10 + d))
        | None => extract_numbers s' (Some d)
        end
      else
        match curr with
        | Some n => n :: extract_numbers s' None
        | None => extract_numbers s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := extract_numbers s None in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "15 apples and 8 oranges" 30 = 7.
Proof.
  reflexivity.
Qed.