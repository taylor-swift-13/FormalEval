Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_neg98 : add_spec 9998 (-98) 9900.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.