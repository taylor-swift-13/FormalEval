Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg999998_neg97: add_spec (-999998) (-97) (-1000095).
Proof.
  unfold add_spec.
  reflexivity.
Qed.