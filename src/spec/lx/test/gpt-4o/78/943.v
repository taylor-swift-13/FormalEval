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

Example hex_key_test_B3ACDF11118872753BD159CEFF723FBCCBB333A191DDBFCBBBD4B37753BDCEE3BD20123456789ABCDEF0137D1DD3BCBB3133A11DDBC :
  hex_key_spec
    ["B"%char; "3"%char; "A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "1"%char; "1"%char; "1"%char; "8"%char; "8"%char; "7"%char; "2"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "1"%char; "5"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "7"%char; "2"%char; "3"%char; "F"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "9"%char; "1"%char; "D"%char; "D"%char; "B"%char; "F"%char; "C"%char; "B"%char; "B"%char; "B"%char; "D"%char; "4"%char; "B"%char; "3"%char; "7"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "C"%char; "E"%char; "E"%char; "3"%char; "B"%char; "D"%char; "2"%char; "0"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "0"%char; "1"%char; "3"%char; "7"%char; "D"%char; "1"%char; "D"%char; "D"%char; "3"%char; "B"%char; "C"%char; "B"%char; "B"%char; "3"%char; "1"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char]
    60.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.