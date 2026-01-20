Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply : multiply_spec 148 412 16.
Proof.
  unfold multiply_spec.
  simpl.
  reflexivity.
Qed.