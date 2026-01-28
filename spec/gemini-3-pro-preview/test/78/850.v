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

Example test_hex_key : hex_key_spec "BB37753BDCEE3BD20123456789ABCDEF0137D1DD3BCBB3133A11DDBCCEEFA12345CEA753BDD67891234567890ABCDEF12345BBAA2202E0ABCDEF12345B1234567890ABCDEFA12345BBA00BAA2202ED" 80.
Proof.
  unfold hex_key_spec.
  simpl.
  reflexivity.
Qed.