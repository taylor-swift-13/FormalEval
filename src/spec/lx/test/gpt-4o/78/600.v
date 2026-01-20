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

Example hex_key_test_753BDCEACDF12345B67C2022EEEFAD890ABCDEF12345BBAA202001111887215E753BD9CEFF23BC337312345B67CEEFABD890ABCDEF12345BBACDF12345B67C2022EEEFAD123ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11DDBC555547567CEEFAD890ABCDEF12345BBAA20200890AB123ABB333A11DDBCBCDEF20202C0CBAABBB2BB333CA11DDBC55554567CEEFAD890ABCDEF12345BBAA2020015E753BD9CEFF231234567890ABCDEF12345BBAA20200BCCBBD4AA20200CBBD431BDCF0 :
  hex_key_spec
    ["7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "C"%char; "E"%char; "A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "2"%char; "0"%char; "2"%char; "2"%char; "E"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "1"%char; "1"%char; "1"%char; "1"%char; "8"%char; "8"%char; "7"%char; "2"%char; "1"%char; "5"%char; "E"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "2"%char; "3"%char; "B"%char; "C"%char; "3"%char; "3"%char; "7"%char; "3"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "E"%char; "E"%char; "F"%char; "A"%char; "B"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "C"%char; "D"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "6"%char; "7"%char; "C"%char; "2"%char; "0"%char; "2"%char; "2"%char; "E"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "1"%char; "2"%char; "3"%char; "A"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "2"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "C"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "5"%char; "5"%char; "5"%char; "5"%char; "4"%char; "7"%char; "5"%char; "6"%char; "7"%char; "C"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "1"%char; "2"%char; "3"%char; "A"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "2"%char; "0"%char; "2"%char; "0"%char; "2"%char; "C"%char; "0"%char; "C"%char; "B"%char; "A"%char; "A"%char; "B"%char; "B"%char; "B"%char; "2"%char; "B"%char; "B"%char; "3"%char; "3"%char; "3"%char; "C"%char; "A"%char; "1"%char; "1"%char; "D"%char; "D"%char; "B"%char; "C"%char; "5"%char; "5"%char; "5"%char; "5"%char; "4"%char; "5"%char; "6"%char; "7"%char; "C"%char; "E"%char; "E"%char; "F"%char; "A"%char; "D"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "1"%char; "5"%char; "E"%char; "7"%char; "5"%char; "3"%char; "B"%char; "D"%char; "9"%char; "C"%char; "E"%char; "F"%char; "F"%char; "2"%char; "3"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "6"%char; "7"%char; "8"%char; "9"%char; "0"%char; "A"%char; "B"%char; "C"%char; "D"%char; "E"%char; "F"%char; "1"%char; "2"%char; "3"%char; "4"%char; "5"%char; "B"%char; "B"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "B"%char; "C"%char; "C"%char; "B"%char; "B"%char; "D"%char; "4"%char; "A"%char; "A"%char; "2"%char; "0"%char; "2"%char; "0"%char; "0"%char; "C"%char; "B"%char; "B"%char; "D"%char; "4"%char; "3"%char; "1"%char; "B"%char; "D"%char; "C"%char; "F"%char; "0"%char]
    186.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.