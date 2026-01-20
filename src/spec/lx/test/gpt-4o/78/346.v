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

Example hex_key_test_ACDF12345B67C2022EEEFAD890AB1232ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF23BCCBBD4 :
  hex_key_spec ["A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "2"%char; "0"%char; "2"%char; "2"%char; "E"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "1"%char; "2"%char; "3"%char; "2"%char; "A"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "2"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "C"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "5"%char; "5"%char; "5"%char; "5"%char; "4"%char; "5"%char; "6"%char; "7"%char; "C"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "1"%char; "5"%char; "E"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "2"%char; "3"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "D"%char; "4"%char] 68.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.