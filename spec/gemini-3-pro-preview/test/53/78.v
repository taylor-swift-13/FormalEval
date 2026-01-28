Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_25_435: add_spec 25 435 460.
Proof.
  unfold add_spec.
  reflexivity.
Qed.