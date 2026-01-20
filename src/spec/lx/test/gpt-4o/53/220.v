Require Import Coq.Arith.Arith.
Require Import Coq.NArith.BinNat.

Definition add_spec (x : N) (y : N) (output : N) : Prop :=
  output = N.add x y.

Example add_test :
  add_spec 999998%N 999998%N 1999996%N.
Proof.
  unfold add_spec.
  reflexivity.
Qed.