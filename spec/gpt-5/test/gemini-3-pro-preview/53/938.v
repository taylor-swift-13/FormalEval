Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_3_neg101 : add_spec 3 (-101) (-98).
Proof.
  unfold add_spec.
  reflexivity.
Qed.