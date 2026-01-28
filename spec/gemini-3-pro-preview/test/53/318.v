Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_large: add_spec 1000000000000000000001 1000000000000000000000 2000000000000000000001.
Proof.
  unfold add_spec.
  reflexivity.
Qed.