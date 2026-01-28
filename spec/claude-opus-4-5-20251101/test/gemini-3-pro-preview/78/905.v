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

Example test_hex_key : hex_key_spec "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDACDF11118872753BD159CEFF723BCCBB333A191BD7BB11ABCD22020DDBB2CC22EECEA5F3BDCEEFAD20201234512134567582290ABCDEFAACDF11118872159CEFF23BCCBBD4A006789CDEF04EFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ACDF1111887C2159CEFFACDF11118872159CEFF12345753BD6789123567890ABCDEF123B45BBAA22020A2202E23BCCBB333A11DDBCBBBD44ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA3137D1DDBB31CEFFEEDDCCBBAADEF0" 228.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.