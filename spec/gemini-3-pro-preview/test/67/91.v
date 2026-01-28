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

Fixpoint parse_nat_aux (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => parse_nat_aux s' (acc * 10 + (nat_of_ascii c - 48))
  end.

Definition parse_Z (s : string) : Z :=
  Z.of_nat (parse_nat_aux s 0).

Fixpoint forallb_string (f : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => f c && forallb_string f s'
  end.

Definition is_number_str (s : string) : bool :=
  match s with
  | EmptyString => false
  | _ => forallb_string is_digit s
  end.

Fixpoint split_aux (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      curr :: split_aux s' EmptyString
    else
      split_aux s' (curr ++ String c EmptyString)
  end.

Definition split (s : string) : list string :=
  split_aux s EmptyString.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let tokens := split s in
  let counts := map (fun t => if is_number_str t then parse_Z t else 0) tokens in
  let total_fruit := fold_right Z.add 0 counts in
  n - total_fruit.

Example fruit_distribution_example : fruit_distribution "24 apples and 18 oranges" 100 = 58.
Proof. reflexivity. Qed.