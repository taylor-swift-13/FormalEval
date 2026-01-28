Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_371_167 : add_spec 371 167 538.
Proof.
  unfold add_spec.
  reflexivity.
Qed.