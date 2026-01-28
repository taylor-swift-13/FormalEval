Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_4_1000 : add_spec 4 1000 1004.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.