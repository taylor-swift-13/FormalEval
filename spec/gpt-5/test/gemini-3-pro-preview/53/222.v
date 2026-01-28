Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_999998_1000000000000000000 : add_spec 999998 1000000000000000000 1000000000000999998.
Proof.
  unfold add_spec.
  reflexivity.
Qed.