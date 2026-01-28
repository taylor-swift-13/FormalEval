Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_67_neg99 : add_spec 67 (-99) (-32).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.