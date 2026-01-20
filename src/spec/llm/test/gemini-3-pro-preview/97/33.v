Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_neg7_neg6 : multiply_spec (-7) (-6) 42.
Proof.
  unfold multiply_spec.
  reflexivity.
Qed.