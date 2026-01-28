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

Fixpoint parse_int_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then
      parse_int_aux s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
    else None
  end.

Definition parse_int (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ => parse_int_aux s 0
  end.

Fixpoint split_string_aux (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      curr :: split_string_aux s' ""
    else
      split_string_aux s' (curr ++ String c EmptyString)
  end.

Definition split_string (s : string) : list string :=
  split_string_aux s "".

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split_string s in
  let nums := map (fun w => match parse_int w with Some v => v | None => 0 end) words in
  n - fold_left Z.add nums 0.

Example test_fruit_distribution : fruit_distribution "20 apples and 0 oranges" 199 = 179.
Proof. reflexivity. Qed.