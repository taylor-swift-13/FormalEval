Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_5_1000000 : add_spec 5 1000000 1000005.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.