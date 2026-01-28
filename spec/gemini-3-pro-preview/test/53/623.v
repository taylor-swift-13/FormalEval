Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg_97_neg_1000000: add_spec (-97) (-1000000) (-1000097).
Proof.
  unfold add_spec.
  reflexivity.
Qed.