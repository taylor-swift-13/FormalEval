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

Fixpoint parse_int_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then parse_int_aux s' (acc * 10 + Z.of_nat (nat_of_ascii c - 48))
    else None
  end.

Definition parse_int (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c s' =>
    match parse_int_aux s 0 with
    | Some n => n
    | None => 0
    end
  end.

Fixpoint split_string (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then curr :: split_string s' ""
    else split_string s' (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let counts := map parse_int words in
  let sum := fold_right Z.add 0 counts in
  n - sum.

Example fruit_distribution_test : fruit_distribution "1 apples and 100 oranges" 120 = 19.
Proof. reflexivity. Qed.