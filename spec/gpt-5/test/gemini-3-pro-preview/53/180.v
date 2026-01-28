Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg249_neg249 : add_spec (-249) (-249) (-498).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.