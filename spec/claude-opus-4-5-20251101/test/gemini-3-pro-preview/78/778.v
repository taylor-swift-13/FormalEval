Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Definition is_prime_hex_digit (c : ascii) : bool :=
  match c with
  | "2"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "B"%char => true
  | "D"%char => true
  | _ => false
  end.

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c rest => c :: string_to_list rest
  end.

Fixpoint count_prime_hex_digits (chars : list ascii) : nat :=
  match chars with
  | [] => 0
  | c :: rest => (if is_prime_hex_digit c then 1 else 0) + count_prime_hex_digits rest
  end.

Definition hex_key_spec (num : string) (result : nat) : Prop :=
  result = count_prime_hex_digits (string_to_list num).

Example test_hex_key : hex_key_spec "1ACDF11118872159CEFF23BCCBBACDF11118872159CEFFACDF1BB37137D1DDBC1118872159CEFF23BCCBB333A11DDBCBBBD44D4234567890ABCDEFA12345BBABA2020CEEFAD11ABCD20C290753BDDDBBCFFEEDDCCBBAA12345BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBCBBBD4437D1DDBC67890ABCDEBF12345BBAA202000" 121.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.