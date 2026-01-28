Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_483_198: add_spec 483 198 681.
Proof.
  unfold add_spec.
  reflexivity.
Qed.