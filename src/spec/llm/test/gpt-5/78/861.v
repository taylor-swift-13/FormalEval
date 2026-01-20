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

Example hex_key_big_nat: hex_key_spec "1ACDF1111887118872159CEFF23BCCBB333A11DDBCBBBD44D4234567890ABCDEFA12345BBABA2020CEEFAD11ABCD20C290753BDDDBBCFFEEDDCCBBAA12345BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBCBBBD4437D1DDBC67890ABCDEBF12345BBAA202000" 99.
Proof.
  unfold hex_key_spec.
  vm_compute.
  reflexivity.
Qed.

Example hex_key_big_Z: Z.of_nat (count_prime_hex "1ACDF1111887118872159CEFF23BCCBB333A11DDBCBBBD44D4234567890ABCDEFA12345BBABA2020CEEFAD11ABCD20C290753BDDDBBCFFEEDDCCBBAA12345BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBCBBBD4437D1DDBC67890ABCDEBF12345BBAA202000") = 99%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.