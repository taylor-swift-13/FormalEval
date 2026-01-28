Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_99_10000: add_spec 99 10000 10099.
Proof.
  unfold add_spec.
  reflexivity.
Qed.