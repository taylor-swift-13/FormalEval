Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1_0 : add_spec 1 0 1.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.