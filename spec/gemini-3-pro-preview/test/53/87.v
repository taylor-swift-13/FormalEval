Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_855_65: add_spec 855 65 920.
Proof.
  unfold add_spec.
  reflexivity.
Qed.