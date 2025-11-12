
Require Import String.
Require Import ZArith.
Require Import Ascii.
Require Import BinNat.
Require Import Nat.

Definition solve_spec (N : nat) (result : string) : Prop :=
  (0 <= N <= 10000)%nat /\
  result = (N.digits 2 (N.sum_digits (Nat.of_num_uint (N.to_string N)))).
