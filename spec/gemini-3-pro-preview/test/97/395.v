Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475612_9876543212 : multiply_spec 2938475612 9876543212 4.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.