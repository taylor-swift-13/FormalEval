Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_4_999999999999999999 : add_spec 4 999999999999999999 1000000000000000003.
Proof.
  unfold add_spec.
  reflexivity.
Qed.