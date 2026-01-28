Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg15_2938475613 : multiply_spec (-15) 2938475613 15.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.