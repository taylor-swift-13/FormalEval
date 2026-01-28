Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_10000_neg16: add_spec 10000 (-16) 9984.
Proof.
  unfold add_spec.
  reflexivity.
Qed.