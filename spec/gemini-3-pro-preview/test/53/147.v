Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg7_neg7: add_spec (-7) (-7) (-14).
Proof.
  unfold add_spec.
  reflexivity.
Qed.