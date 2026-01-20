Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition to_digit (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_Z_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then parse_Z_aux s' (acc * 10 + to_digit c)
    else None
  end.

Definition parse_Z (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => parse_Z_aux s 0
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

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_aux s "" in
  let counts := map (fun w => match parse_Z w with | Some v => v | None => 0 end) words in
  n - fold_right Z.add 0 counts.

Example test_fruit_distribution : fruit_distribution "10 apples and 0 oranges" 30 = 20.
Proof.
  compute.
  reflexivity.
Qed.