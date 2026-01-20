Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_2938475609_6789 : multiply_spec 2938475609 6789 81.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.