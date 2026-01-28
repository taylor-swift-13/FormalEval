Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_999999_999998: add_spec 999999 999998 1999997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.