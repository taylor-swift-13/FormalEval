Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10001_999999 : add_spec 10001 999999 1010000.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.