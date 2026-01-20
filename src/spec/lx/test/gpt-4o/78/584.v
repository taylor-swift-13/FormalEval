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

Example hex_key_test_ACD7C200015E753BD9CEFF23BCCBBD4 :
  hex_key_spec ["A"%char; "C"%char; "D"%char; "7"%char; "C"%char; "2"%char; "0"%char; "0"%char; "0"%char; "1"%char; "5"%char; "E"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "2"%char; "3"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "D"%char; "4"%char] 15.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.