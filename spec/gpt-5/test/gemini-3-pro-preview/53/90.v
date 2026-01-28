Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_420_134 : add_spec 420 134 554.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.