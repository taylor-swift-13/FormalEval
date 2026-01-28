Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_97_neg10: add_spec 97 (-10) 87.
Proof.
  unfold add_spec.
  reflexivity.
Qed.