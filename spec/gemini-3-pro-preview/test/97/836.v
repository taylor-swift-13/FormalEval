Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_6789_246813582 : multiply_spec 6789 246813582 18.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.