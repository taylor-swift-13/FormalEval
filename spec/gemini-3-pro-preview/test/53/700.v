Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg103_1000: add_spec (-103) 1000 897.
Proof.
  unfold add_spec.
  reflexivity.
Qed.