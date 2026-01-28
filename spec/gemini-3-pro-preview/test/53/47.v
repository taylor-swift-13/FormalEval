Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_30_177: add_spec 30 177 207.
Proof.
  unfold add_spec.
  reflexivity.
Qed.