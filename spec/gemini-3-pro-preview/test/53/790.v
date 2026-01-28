Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg103_neg103: add_spec (-103) (-103) (-206).
Proof.
  unfold add_spec.
  reflexivity.
Qed.