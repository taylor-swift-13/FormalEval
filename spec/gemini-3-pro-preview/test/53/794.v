Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_66_66: add_spec 66 66 132.
Proof.
  unfold add_spec.
  reflexivity.
Qed.