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

Example test_hex_key : hex_key_spec "BBBB11ABCD22020DDBB2CC22EECEA3D1BBB313D1721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BCEBB37137D1DDBCBB31373A11DDBCEFAD11ABCD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA2007D1DDBB1CB3D137D1DDBC3B7DD1DDBC" 157.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.