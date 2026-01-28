Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9998_9998: add_spec 9998 9998 19996.
Proof.
  unfold add_spec.
  reflexivity.
Qed.