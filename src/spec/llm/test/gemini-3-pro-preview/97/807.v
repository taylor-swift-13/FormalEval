Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg975312469_neg97 : multiply_spec (-975312469) (-97) 63.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.