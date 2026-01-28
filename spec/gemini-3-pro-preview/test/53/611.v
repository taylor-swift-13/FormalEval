Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg97_neg999998: add_spec (-97) (-999998) (-1000095).
Proof.
  unfold add_spec.
  reflexivity.
Qed.