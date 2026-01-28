Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Local Open Scope string_scope.
Local Open Scope nat_scope.

Definition prime_hex_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  Nat.eqb n 50 || Nat.eqb n 51 || Nat.eqb n 53 || Nat.eqb n 55 || Nat.eqb n 66 || Nat.eqb n 68.

Fixpoint count_prime_hex (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => Nat.add (if prime_hex_digit c then 1 else 0) (count_prime_hex rest)
  end.

Definition hex_key_spec (num : string) (count : nat) : Prop :=
  count = count_prime_hex num.

Example test_hex_key_long : hex_key_spec "11ABCD22020DDBB12345B67C2022EEEFAD890ABAB4CDEF202020CBAABBBDDDDDDCCCCC111112345B67C1BB333AB4CDEF202020CBAABBB5DDDDDDCCCCC111112212345B67CEEFAD890ABCDEF12345BBAA2020033CEEEF753BDCEEFAD2020123456789ABCDEABCDEF202020CBAABBBDDDDDDCCCCC1111122222333334444455555F0EAED44444555555A113DDBC20012212345B67CEEFAD890ABCDEF12345BBAA2020033444555555CDEF12345BBBBAA" 168.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.