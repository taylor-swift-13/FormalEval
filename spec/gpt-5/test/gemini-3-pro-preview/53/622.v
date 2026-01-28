Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9999_neg2 : add_spec (-9999) (-2) (-10001).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.