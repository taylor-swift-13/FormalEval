Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_large : add_spec 999999999999999999999 (-999998) 999999999999999000001.
Proof.
  unfold add_spec.
  reflexivity.
Qed.