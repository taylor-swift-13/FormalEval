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

Example hex_key_large_nat: hex_key_spec "17212BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBBBDBC34567890ABCDEAF12345BBAA22012334567890ABCDEFA123435BBAA20200345BBAAA200" 61.
Proof.
  unfold hex_key_spec.
  vm_compute.
  reflexivity.
Qed.

Example hex_key_large_Z: Z.of_nat (count_prime_hex "17212BB31ACDF11118872F159CEFFACDF11118872159CEFF23BCCBB333A11DDBBBDBC34567890ABCDEAF12345BBAA22012334567890ABCDEFA123435BBAA20200345BBAAA200") = 61%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.