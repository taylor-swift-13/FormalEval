Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_6_1 : add_spec 6 1 7.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.