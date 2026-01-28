Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers_aux (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c s' =>
      if is_digit c then
        let d := char_to_Z c in
        match acc with
        | Some n => extract_numbers_aux s' (Some (n * 10 + d))
        | None => extract_numbers_aux s' (Some d)
        end
      else
        match acc with
        | Some n => n :: extract_numbers_aux s' None
        | None => extract_numbers_aux s' None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := extract_numbers_aux s None in
  let sum := fold_left Z.add numbers 0 in
  n - sum.

Example test_fruit_distribution: fruit_distribution "0 apples and 0 oranges" 106 = 106.
Proof. reflexivity. Qed.