Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9999_neg999997: add_spec (-9999) (-999997) (-1009996).
Proof.
  unfold add_spec.
  reflexivity.
Qed.