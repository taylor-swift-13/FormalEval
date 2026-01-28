Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999999_neg11: add_spec (-999999) (-11) (-1000010).
Proof.
  unfold add_spec.
  reflexivity.
Qed.