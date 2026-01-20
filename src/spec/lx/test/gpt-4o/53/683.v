Require Import Coq.Arith.Arith.
Require Import Coq.NArith.BinNat.

Definition add_spec (x : nat) (y : nat) (output : nat) : Prop :=
  output = x + y.

Example add_test :
  add_spec 5 (N.to_nat 1000000) (N.to_nat 1000005).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.