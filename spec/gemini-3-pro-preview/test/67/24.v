Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_int_aux (s : string) (acc : Z) : option Z :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then parse_int_aux s' (acc * 10 + char_to_Z c)
    else None
  end.

Definition parse_int (s : string) : Z :=
  match s with
  | EmptyString => 0
  | _ => match parse_int_aux s 0 with
         | Some n => n
         | None => 0
         end
  end.

Fixpoint tokens (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => if string_dec acc "" then [] else [acc]
  | String c s' =>
    if (nat_of_ascii c =? 32)%nat then
      if string_dec acc "" then tokens s' ""
      else acc :: tokens s' ""
    else tokens s' (acc ++ String c EmptyString)
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := tokens s "" in
  let counts := map parse_int words in
  n - fold_left Z.add counts 0.

Example fruit_distribution_example : fruit_distribution "0 apples and 0 oranges" 30 = 30.
Proof. reflexivity. Qed.