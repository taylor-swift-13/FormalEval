Require Import Coq.Arith.Arith.

Definition add_spec (x : nat) (y : nat) (output : nat) : Prop :=
  output = x + y.

Example add_test :
  add_spec 890 180 1070.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.