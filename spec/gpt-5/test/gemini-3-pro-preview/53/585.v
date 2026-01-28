Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg98_neg99 : add_spec (-98) (-99) (-197).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.