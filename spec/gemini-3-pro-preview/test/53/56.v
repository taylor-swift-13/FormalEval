Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_670_359: add_spec 670 359 1029.
Proof.
  unfold add_spec.
  reflexivity.
Qed.