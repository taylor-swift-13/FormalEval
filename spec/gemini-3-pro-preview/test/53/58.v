Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_265_822: add_spec 265 822 1087.
Proof.
  unfold add_spec.
  reflexivity.
Qed.