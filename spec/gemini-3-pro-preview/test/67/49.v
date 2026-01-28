Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint parse_Z_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then
      parse_Z_aux s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
    else None
  end.

Definition parse_Z (s : string) : Z :=
  match parse_Z_aux s 0 with
  | Some z => z
  | None => 0
  end.

Fixpoint split_aux (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      curr :: split_aux s' ""
    else
      split_aux s' (curr ++ String c EmptyString)
  end.

Definition split (s : string) : list string :=
  split_aux s "".

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split s in
  let counts := map parse_Z words in
  n - fold_right Z.add 0 counts.

Example test_fruit_distribution : fruit_distribution "0 apples and 1 oranges" 4 = 3.
Proof. reflexivity. Qed.