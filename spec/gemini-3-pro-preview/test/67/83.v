Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint extract_numbers (s : string) (acc : option Z) : list Z :=
  match s with
  | EmptyString => 
      match acc with 
      | Some n => [n] 
      | None => [] 
      end
  | String c rest =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        match acc with
        | Some n => extract_numbers rest (Some (n * 10 + d))
        | None => extract_numbers rest (Some d)
        end
      else
        match acc with
        | Some n => n :: extract_numbers rest None
        | None => extract_numbers rest None
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let numbers := extract_numbers s None in
  let sum := fold_left Z.add numbers 0 in
  n - sum.

Example test_fruit_distribution: fruit_distribution "1 apples and 99 oranges" 100 = 0.
Proof.
  compute.
  reflexivity.
Qed.