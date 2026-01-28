Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_6_1000000000000000000: add_spec 6 1000000000000000000 1000000000000000006.
Proof.
  unfold add_spec.
  reflexivity.
Qed.