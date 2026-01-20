Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Local Open Scope string_scope.
Local Open Scope Z_scope.

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

Example hex_key_large_nat: hex_key_spec "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA12345BBAA20200BCC22EBB3137D1DDBB31CEFFEEDDCCBBAADEF0" 124.
Proof.
  unfold hex_key_spec.
  vm_compute.
  reflexivity.
Qed.

Example hex_key_large_Z: Z.of_nat (count_prime_hex "753BDCEEFAD2020121721234567890ABCDEF12345BBAA22012334567890ABCDEFA12345BBB3137D1DDBB31CBAA202002E345BBAAA200456789C11ABCD2020DDB1ACDF11118872159CEFF23BCCBBD423456711ABCD2020753BDDDBBBCFFEEDDCCBBAA890ABCDEFA12345BBAA20200BCC22EBB3137D1DDBB31CEFFEEDDCCBBAADEF0") = 124%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.