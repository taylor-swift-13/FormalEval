Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_987653_2938475610 : multiply_spec 987653 2938475610 0.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.