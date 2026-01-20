Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387463_246813580 : multiply_spec 1092387463 246813580 0.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.