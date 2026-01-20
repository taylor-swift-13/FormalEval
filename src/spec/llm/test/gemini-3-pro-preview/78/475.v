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

Example test_hex_key : hex_key_spec "AB4CDEF202020CBAABBBDDDDDDCCCCC111112345B67C1BB333AB4CDEF202020CBAABBB5DDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033CEEEF753BDCEEFAD2020123456789ABCDEABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555F0E73ABB333A11DDBCBCDEF202020CBAABBB2BB333CA11D0DBC555520012212345B67CEEFAD890ABCDEF12345BBAA2020033444555555" 162.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.