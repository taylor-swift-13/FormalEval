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

Example hex_key_test_ACDFC11118872159C172345BB11ABCD2020DDBBCC22EECEAAA202003BCCBBD4 :
  hex_key_spec ["A"%char; "C"%char; "D"%char; "F"%char; "C"%char; "1"%char; "1"%char; "1"%char; "1"%char; "8"%char; "8"%char; "7"%char; "2"%char; "1"%char; "5"%char; "9"%char; "C"%char; "1"%char; "7"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "1"%char; "1"%char; "A"%char; "B"%char; "C"%char; "D"%char; "2"%char; "0"%char; "2"%char; "0"%char; "D"%char; "D"%char; "B"%char; "B"%char; "C"%char; "C"%char; "2"%char; "2"%char; "E"%char; "E"%char; "C"%char; "E"%char; "A"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "3"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "D"%char; "4"%char] 27.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.