Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_1092387465_1092387463 : multiply_spec 1092387465 1092387463 15.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.