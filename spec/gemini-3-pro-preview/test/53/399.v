Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9999_big: add_spec (-9999) 1000000000000000000001 999999999999999990002.
Proof.
  unfold add_spec.
  reflexivity.
Qed.