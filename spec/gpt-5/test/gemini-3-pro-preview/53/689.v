Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_1000000_neg_9999 : add_spec (-1000000) (-9999) (-1009999).
Proof.
  unfold add_spec.
  reflexivity.
Qed.