Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10002_1000000000000000000: add_spec 10002 1000000000000000000 1000000000000010002.
Proof.
  unfold add_spec.
  reflexivity.
Qed.