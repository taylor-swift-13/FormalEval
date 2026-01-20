Require Import Coq.Arith.Arith.

Definition add_spec (x : bool) (y : bool) (output : nat) : Prop :=
  output = Nat.b2n x + Nat.b2n y.

Example add_test :
  add_spec false true 1.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.