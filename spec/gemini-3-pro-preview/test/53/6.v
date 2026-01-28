Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_480_593: add_spec 480 593 1073.
Proof.
  unfold add_spec.
  reflexivity.
Qed.