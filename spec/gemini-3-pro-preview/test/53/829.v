Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg10_neg2: add_spec (-10) (-2) (-12).
Proof.
  unfold add_spec.
  reflexivity.
Qed.