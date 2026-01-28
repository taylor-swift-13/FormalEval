Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10001_9997: add_spec 10001 9997 19998.
Proof.
  unfold add_spec.
  reflexivity.
Qed.