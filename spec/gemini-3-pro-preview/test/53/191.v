Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg2_10001: add_spec (-2) 10001 9999.
Proof.
  unfold add_spec.
  reflexivity.
Qed.