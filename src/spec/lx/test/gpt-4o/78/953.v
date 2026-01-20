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

Example hex_key_test_BBBB11ABCD22020DDBB2CC22EECEA3D1BBB313D1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BCEBB37137D1DDBCBB31373A11DDBCEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA2007D1DDBB1CB3D137D1DDBC3B7DD1DDBC :
  hex_key_spec ["B"%char; "B"%char; "B"%char; "B"%char; "1"%char; "1"%char; "A"%char; "B"%char; "C"%char; "D"%char; "2"%char; "2"%char; "0"%char; "2"%char; "0"%char; "D"%char; "D"%char; "B"%char; "B"%char; "2"%char; "C"%char; "C"%char; "2"%char; "2"%char; "E"%char; "E"%char; "C"%char; "E"%char; "A"%char; "3"%char; "D"%char; "1"%char; "B"%char; "B"%char; "B"%char; "3"%char; "1"%char; "3"%char; "D"%char; "1"%char; "7"%char; "2"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "2"%char; "0"%char; "1"%char; "2"%char; "3"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "A"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "C"%char; "E"%char; "B"%char; "B"%char; "3"%char; "7"%char; "1"%char; "3"%char; "7"%char; "D"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "B"%char; "3"%char; "1"%char; "3"%char; "7"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "E"%char; "F"%char; "A"%char; "D"%char; "1"%char; "1"%char; "A"%char; "B"%char; "C"%char; "D"%char; "2"%char; "0"%char; "C"%char; "2"%char; "0"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "D"%char; "D"%char; "B"%char; "B"%char; "C"%char; "F"%char; "F"%char; "E"%char; "E"%char; "D"%char; "D"%char; "C"%char; "C"%char; "B"%char; "B"%char; "A"%char; "A"%char; "1"%char; "A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "1"%char; "1"%char; "1"%char; "8"%char; "8"%char; "7"%char; "2"%char; "1"%char; "5"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "1"%char; "1"%char; "1"%char; "8"%char; "8"%char; "7"%char; "2"%char; "1"%char; "5"%char; "9"%char; "C"%char; "D"%char; "E"%char; "F"%char; "F"%char; "2"%char; "3"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "B"%char; "B"%char; "D"%char; "4"%char; "4"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "2"%char; "E"%char; "3"%char; "4"%char; "5"%char; "B"%char; "7"%char; "B"%char; "A"%char; "A"%char; "A"%char; "2"%char; "0"%char; "0"%char; "7"%char; "D"%char; "1"%char; "D"%char; "D"%char; "B"%char; "B"%char; "1"%char; "C"%char; "B"%char; "3"%char; "D"%char; "1"%char; "3"%char; "7"%char; "D"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "3"%char; "B"%char; "7"%char; "D"%char; "D"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char] 157.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.