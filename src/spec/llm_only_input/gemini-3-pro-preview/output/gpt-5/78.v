Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

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

Example test_hex_key_AB : hex_key_spec "AB" 1.
Proof.
  (* Unfold the specification definition *)
  unfold hex_key_spec.
  
  (* 
     Compute the value of (count_prime_hex "AB").
     
     Analysis:
     1. "A" is ascii 65. 
        prime_hex_digit checks: 65 in {50,51,53,55,66,68}? False.
        Adds 0.
     2. "B" is ascii 66.
        prime_hex_digit checks: 66 in {50,51,53,55,66,68}? True (matches 66).
        Adds 1.
     
     Total = 0 + 1 = 1.
  *)
  compute.
  
  (* The goal reduces to 1 = 1 *)
  reflexivity.
Qed.