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

Example hex_key_test_ABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555 :
  hex_key_spec
    ["A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "D"%char; "D"%char; "D"%char; "D"%char; "D"%char; "D"%char; "C"%char; "C"%char; "C"%char; "C"%char; "C"%char; "1"%char; "1"%char; "1"%char; "1"%char; "1"%char; "2"%char; "2"%char; "2"%char; "2"%char; "2"%char; "3"%char; "3"%char; "3"%char; "3"%char; "3"%char; "4"%char; "4"%char; "4"%char; "4"%char; "4"%char; "5"%char; "5"%char; "5"%char; "5"%char; "5"%char]
    30.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.