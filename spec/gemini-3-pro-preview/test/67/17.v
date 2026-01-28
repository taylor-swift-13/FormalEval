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

Fixpoint parse_nat (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then
      parse_nat s' (10 * acc + (nat_of_ascii c - 48))%nat
    else None
  end.

Definition string_to_Z (s : string) : Z :=
  match parse_nat s 0 with
  | Some n => Z.of_nat n
  | None => 0
  end.

Fixpoint split_string (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
    if (ascii_dec c " ") then
      curr :: split_string s' ""
    else
      split_string s' (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let amounts := map string_to_Z words in
  let sum := fold_right Z.add 0 amounts in
  n - sum.

Example fruit_distribution_example : fruit_distribution "8 apples and 2 oranges" 15 = 5.
Proof. reflexivity. Qed.