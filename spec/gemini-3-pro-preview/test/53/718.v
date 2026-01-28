Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_9999_neg10: add_spec 9999 (-10) 9989.
Proof.
  unfold add_spec.
  reflexivity.
Qed.