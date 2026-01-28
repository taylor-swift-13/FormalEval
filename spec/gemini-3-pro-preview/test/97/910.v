Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg_12346_neg_975312469 : multiply_spec (-12346) (-975312469) 54.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.