Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_574_555: add_spec 574 555 1129.
Proof.
  unfold add_spec.
  reflexivity.
Qed.