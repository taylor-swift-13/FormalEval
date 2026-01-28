Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_390_904: add_spec 390 904 1294.
Proof.
  unfold add_spec.
  reflexivity.
Qed.