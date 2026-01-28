Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg250_neg250: add_spec (-250) (-250) (-500).
Proof.
  unfold add_spec.
  reflexivity.
Qed.