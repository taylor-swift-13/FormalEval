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

Example test_hex_key_232 : hex_key_spec "232" 3.
Proof.
  unfold hex_key_spec.
  simpl.
  (* 
     '2' is ASCII 50. 
     '3' is ASCII 51.
     prime_hex_digit '2' checks: 50 = 50 -> True.
     prime_hex_digit '3' checks: 51 = 51 -> True.
     prime_hex_digit '2' checks: 50 = 50 -> True.
     Result is 1 + 1 + 1 = 3.
  *)
  reflexivity.
Qed.