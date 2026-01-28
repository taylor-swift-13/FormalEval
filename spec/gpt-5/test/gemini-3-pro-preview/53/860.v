Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_99_neg_1000000000000000000000 : add_spec (-99) (-1000000000000000000000) (-1000000000000000000099).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.