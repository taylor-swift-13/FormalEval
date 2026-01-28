Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1002_0 : add_spec 1002 0 1002.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.