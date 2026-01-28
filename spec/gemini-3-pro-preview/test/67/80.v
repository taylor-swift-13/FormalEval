Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Fixpoint parse_nat (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' =>
    if is_digit c then parse_nat s' (acc * 10 + (nat_of_ascii c - 48))
    else acc
  end.

Definition parse_int (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c _ =>
    if is_digit c then Z.of_nat (parse_nat s 0)
    else 0
  end.

Fixpoint split_string (s : string) (cur : string) : list string :=
  match s with
  | EmptyString => if string_dec cur "" then [] else [cur]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      if string_dec cur "" then split_string s' ""
      else cur :: split_string s' ""
    else split_string s' (cur ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let numbers := map parse_int words in
  let sum := fold_right Z.add 0 numbers in
  n - sum.

Example test_fruit_distribution: fruit_distribution "1 apples and 99 oranges" 105 = 5.
Proof. reflexivity. Qed.