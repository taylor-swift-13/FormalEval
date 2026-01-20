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

Example hex_key_test_C753BDCDEDF0C753BDCDEDF0 :
  hex_key_spec ["C"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "C"%char; "D"%char; "E"%char; "D"%char; "F"%char; "0"%char; "C"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "C"%char; "D"%char; "E"%char; "D"%char; "F"%char; "0"%char] 14.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.