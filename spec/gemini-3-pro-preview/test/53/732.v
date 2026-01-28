Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_66_2: add_spec 66 2 68.
Proof.
  unfold add_spec.
  reflexivity.
Qed.