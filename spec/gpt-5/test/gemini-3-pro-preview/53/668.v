Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_66_neg_1000000000000000000000 : add_spec 66 (-1000000000000000000000) (-999999999999999999934).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.