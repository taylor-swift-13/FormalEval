Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg10000_neg99 : add_spec (-10000) (-99) (-10099).
Proof.
  unfold add_spec.
  reflexivity.
Qed.