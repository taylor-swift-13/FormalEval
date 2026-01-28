Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_124_732: add_spec 124 732 856.
Proof.
  unfold add_spec.
  reflexivity.
Qed.