Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg101_3 : add_spec (-101) 3 (-98).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.