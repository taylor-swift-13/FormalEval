Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_270_420: add_spec 270 420 690.
Proof.
  unfold add_spec.
  reflexivity.
Qed.