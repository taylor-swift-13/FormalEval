Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 999999999999999999998 (-10001) 999999999999999989997.
Proof.
  unfold add_spec.
  reflexivity.
Qed.