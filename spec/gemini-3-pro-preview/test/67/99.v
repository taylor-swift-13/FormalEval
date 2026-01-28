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

Fixpoint extract_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString =>
      match acc with
      | Some n => [n]
      | None => []
      end
  | String c rest =>
      if is_digit c then
        let d := digit_to_Z c in
        let new_acc := match acc with
                       | Some n => n * 10 + d
                       | None => d
                       end in
        extract_numbers rest (Some new_acc)
      else
        match acc with
        | Some n => n :: extract_numbers rest None
        | None => extract_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := extract_numbers s None in
  n - fold_right Z.add 0 numbers.

Example fruit_distribution_example : fruit_distribution "3 apples and 7 oranges" 198 = 188.
Proof.
  compute.
  reflexivity.
Qed.