Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg9996_neg1000001: add_spec (-9996) (-1000001) (-1009997).
Proof.
  unfold add_spec.
  reflexivity.
Qed.