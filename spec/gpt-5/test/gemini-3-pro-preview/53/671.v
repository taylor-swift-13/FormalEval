Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_2_1 : add_spec 2 1 3.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.