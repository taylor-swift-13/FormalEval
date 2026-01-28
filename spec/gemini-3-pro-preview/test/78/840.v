Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Open Scope string_scope.
Open Scope char_scope.

Definition is_prime_hex (c : ascii) : bool :=
  match c with
  | "2" => true
  | "3" => true
  | "5" => true
  | "7" => true
  | "B" => true
  | "D" => true
  | _ => false
  end.

Fixpoint count_primes (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => 
      (if is_prime_hex c then 1 else 0) + count_primes rest
  end.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = count_primes num.

Example test_hex_key : hex_key_spec "172345BBAAACDF11111721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBAA202002CEEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1234567890ABCDEF12345BBAA20200EFF723BCCBB311ABCD2020DDBBCEC22EEFFEEDDCCBBAA33A191DDBFCBBBD42A20200" 101.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.