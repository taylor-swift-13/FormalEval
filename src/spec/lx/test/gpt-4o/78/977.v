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

Example hex_key_test_75F3BD11ABCD2BAACEEFAD20201234567D89CDEF0 :
  hex_key_spec ["7"%char; "5"%char; "F"%char; "3"%char; "B"%char; "D"%char; "1"%char; "1"%char; "A"%char; "B"%char; "C"%char; "D"%char; "2"%char; "B"%char; "A"%char; "A"%char; "C"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "2"%char; "0"%char; "2"%char; "0"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "D"%char; "8"%char; "9"%char; "C"%char; "D"%char; "E"%char; "F"%char; "0"%char] 18.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.