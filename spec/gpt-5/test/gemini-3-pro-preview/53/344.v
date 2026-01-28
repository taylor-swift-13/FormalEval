Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg98_neg999999 : add_spec (-98) (-999999) (-1000097).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.