Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg13_neg4 : multiply_spec (-13) (-4) 12.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.