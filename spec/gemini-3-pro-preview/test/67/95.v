Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n)%nat && (n <=? 57)%nat)%bool.

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_int_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c rest =>
      if is_digit c then parse_int_aux rest (acc * 10 + to_digit c)
      else None
  end.

Definition parse_int (s : string) : option Z :=
  match s with
  | EmptyString => None
  | String c rest =>
      if is_digit c then parse_int_aux rest (to_digit c)
      else None
  end.

Fixpoint split_string (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => if (String.length curr =? 0)%nat then [] else [curr]
  | String c rest =>
      if (nat_of_ascii c =? 32)%nat then
        if (String.length curr =? 0)%nat then split_string rest ""
        else curr :: split_string rest ""
      else split_string rest (curr ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s "" in
  let counts := map (fun w => match parse_int w with Some v => v | None => 0 end) words in
  n - fold_right Z.add 0 counts.

Example test_fruit_distribution: fruit_distribution "1 apples and 99 oranges" 104 = 4.
Proof.
  compute.
  reflexivity.
Qed.