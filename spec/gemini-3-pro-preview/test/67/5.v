From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Lists.List.
From Coq Require Import ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Fixpoint parse_Z_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then
      parse_Z_aux s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
    else None
  end.

Definition parse_Z (s : string) : option Z :=
  match s with
  | EmptyString => None
  | String c s' => parse_Z_aux s 0
  end.

Fixpoint split_aux (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => if (String.length curr =? 0)%nat then [] else [curr]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      if (String.length curr =? 0)%nat then split_aux s' ""
      else curr :: split_aux s' ""
    else
      split_aux s' (curr ++ String c EmptyString)
  end.

Definition split (s : string) : list string := split_aux s "".

Fixpoint sum_valid_numbers (l : list string) : Z :=
  match l with
  | [] => 0
  | s :: rest =>
    match parse_Z s with
    | Some z => z + sum_valid_numbers rest
    | None => sum_valid_numbers rest
    end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let parts := split s in
  let sum := sum_valid_numbers parts in
  n - sum.

Example example_fruit_distribution : fruit_distribution "2 apples and 3 oranges" 100 = 95.
Proof. reflexivity. Qed.