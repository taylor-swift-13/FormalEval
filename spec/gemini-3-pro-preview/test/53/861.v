Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_99_10001: add_spec 99 10001 10100.
Proof.
  unfold add_spec.
  reflexivity.
Qed.