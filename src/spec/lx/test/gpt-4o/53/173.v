Require Import Coq.Arith.Arith.

Definition add_spec (x : nat) (y : nat) (output : nat) : Prop :=
  output = x + y.

Example add_test :
  add_spec 10001 10000 20001.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.