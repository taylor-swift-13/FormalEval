Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg9997_neg1000000 : add_spec (-9997) (-1000000) (-1009997).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.