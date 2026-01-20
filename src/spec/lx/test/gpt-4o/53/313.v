Require Import Coq.Arith.Arith.

Definition add_spec (x : bool) (y : bool) (output : nat) : Prop :=
  output = (if x then 1 else 0) + (if y then 1 else 0).

Example add_test :
  add_spec false false 0.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.