Require Import Coq.Arith.Arith.

Definition add_spec (x : nat) (y : nat) (output : nat) : Prop :=
  output = x + y.

Example add_test :
  add_spec 0 9998 9998.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.