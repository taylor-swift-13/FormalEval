Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 48 n) && (Nat.leb n 57).

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint extract_numbers_aux (s : string) (curr : Z) (reading : bool) : list Z :=
  match s with
  | EmptyString => if reading then [curr] else []
  | String c rest =>
      if is_digit c then
        extract_numbers_aux rest (curr * 10 + digit_to_Z c) true
      else
        if reading then curr :: extract_numbers_aux rest 0 false
        else extract_numbers_aux rest 0 false
  end.

Definition extract_numbers (s : string) : list Z :=
  extract_numbers_aux s 0 false.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - fold_right Z.add 0 (extract_numbers s).

Example test_fruit_distribution : fruit_distribution "10 apples and 20 oranges" 30 = 0.
Proof.
  compute.
  reflexivity.
Qed.