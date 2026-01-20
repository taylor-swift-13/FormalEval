Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char | "3"%char | "5"%char | "7"%char | "B"%char | "D"%char => true
  | _ => false
  end.

Fixpoint count_prime_hex (l : list ascii) : nat :=
  match l with
  | [] => 0
  | h :: t =>
      (if is_prime_hex_digit h then 1 else 0) + count_prime_hex t
  end.

Definition hex_key_spec (s : list ascii) (n : nat) : Prop :=
  n = count_prime_hex s.

Example hex_key_test_771679D99999ABCD2371C679D999799A9B7CD23777 :
  hex_key_spec ["7"%char; "7"%char; "1"%char; "6"%char; "7"%char; "9"%char; "D"%char; "9"%char; "9"%char; "9"%char; "9"%char; "A"%char; "B"%char; "C"%char; "D"%char; "2"%char; "3"%char; "7"%char; "1"%char; "C"%char; "6"%char; "7"%char; "9"%char; "D"%char; "9"%char; "9"%char; "9"%char; "7"%char; "9"%char; "9"%char; "A"%char; "9"%char; "B"%char; "7"%char; "C"%char; "D"%char; "2"%char; "3"%char; "7"%char; "7"%char; "7"%char] 20.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.