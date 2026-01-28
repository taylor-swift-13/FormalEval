Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_1000000000000000000000_10000: add_spec 1000000000000000000000 10000 1000000000000000010000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.