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

Example test_hex_key_long : hex_key_spec "BB31A7531234567891234567890ABCDEF12345BBAA2202E0ABCDEF12345BBAA2202EBDCEEFAD1234567890ABCDEF12345BBAA22012345678900ABCDEFEA12345CACE1721234567890ABCDEF12345BBAA2201233CD20C20753BDDDBBCFFEEDDCCBBAA1ACDF11118872159CEFFACDF11118B872159CDEFF23BCCBB333A11DDBCBBBD44234567890ABCDEF12345BBAA20200BAA202002E345B7BAAA200ADEADBBAA202002EDDBC753BD" 156.
Proof.
  unfold hex_key_spec.
  reflexivity.
Qed.