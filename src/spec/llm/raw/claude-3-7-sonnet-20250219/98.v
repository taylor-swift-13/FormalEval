
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_uppercase_vowel (c : ascii) : bool :=
  match c with
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Fixpoint count_upper_even_aux (s : string) (idx : nat) : nat :=
  match s with
  | EmptyString => 0
  | String c rest =>
    let count_here := if (Nat.even idx) && is_uppercase_vowel c then 1 else 0 in
    count_here + count_upper_even_aux rest (S idx)
  end.

Definition count_upper_spec (s : string) (cnt : nat) : Prop :=
  cnt = count_upper_even_aux s 0.
