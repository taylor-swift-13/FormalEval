Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_14_neg15 : multiply_spec 14 (-15) 20.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.