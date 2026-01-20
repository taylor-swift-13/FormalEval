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

Example hex_key_test_CE73ABB333A11DDBCBCDEF20753BDCEEFFA7F89ABCDEF02011ACD2020DDBB12345B67C2022EEEFAD890ABCDE12345B67C2022EEEFAD890ABCFDEF275373ABB3033A11DDBCBCDEF202020CBAABBB2BB333CA11D0DBC5555EF002E12345BBAA20200F12345BBBBAA20CBAABBB2BB333CA11DDEFEAD :
  hex_key_spec ["C"%char; "E"%char; "7"%char; "3"%char; "A"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "C"%char; "E"%char; "E"%char; "F"%char; "F"%char; "A"%char; "7"%char; "F"%char; "8"%char; "9"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "0"%char; "2"%char; "0"%char; "1"%char; "1"%char; "A"%char; "C"%char; "D"%char; "2"%char; "0"%char; "2"%char; "0"%char; "D"%char; "D"%char; "B"%char; "B"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "2"%char; "0"%char; "2"%char; "2"%char; "E"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "2"%char; "0"%char; "2"%char; "2"%char; "E"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "F"%char; "D"%char; "E"%char; "F"%char; "2"%char; "7"%char; "5"%char; "3"%char; "7"%char; "3"%char; "A"%char; "B"%char; "B"%char; "3"%char; "0"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "2"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "C"%char; "A"%char; "1"%char; "1"%char; "D"%char; "0"%char; "D"%char; "B"%char; "C"%char; "5"%char; "5"%char; "5"%char; "5"%char; "E"%char; "F"%char; "0"%char; "0"%char; "2"%char; "E"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "2"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "C"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "E"%char; "F"%char; "E"%char; "A"%char; "D"%char] 116.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.