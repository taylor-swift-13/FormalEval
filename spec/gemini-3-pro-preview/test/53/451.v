Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10003_5: add_spec 10003 5 10008.
Proof.
  unfold add_spec.
  reflexivity.
Qed.