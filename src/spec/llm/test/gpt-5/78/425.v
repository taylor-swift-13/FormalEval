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

Example hex_key_big_nat: hex_key_spec "ACDF123AB11DDBC5555753BD45B633A11DDBCBBCDEF202020CB2022EAABBB2BB333CA11DDBC55554567753FBDCEE753BDF01234567CEEFAD89073533ABCDEF12345BBAA20200EEFAD890ABCDEF12345BBAA2020015E75CBBD4" 96.
Proof.
  unfold hex_key_spec.
  vm_compute.
  reflexivity.
Qed.

Example hex_key_big_Z: Z.of_nat (count_prime_hex "ACDF123AB11DDBC5555753BD45B633A11DDBCBBCDEF202020CB2022EAABBB2BB333CA11DDBC55554567753FBDCEE753BDF01234567CEEFAD89073533ABCDEF12345BBAA20200EEFAD890ABCDEF12345BBAA2020015E75CBBD4") = 96%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.