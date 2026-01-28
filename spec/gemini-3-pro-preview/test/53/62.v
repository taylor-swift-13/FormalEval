Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_457_319: add_spec 457 319 776.
Proof.
  unfold add_spec.
  reflexivity.
Qed.