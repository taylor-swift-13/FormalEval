Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999998_neg9999 : add_spec 999998 (-9999) 989999.
Proof.
  unfold add_spec.
  reflexivity.
Qed.