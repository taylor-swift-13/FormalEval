Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_670_359 : add_spec 670 359 1029.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.