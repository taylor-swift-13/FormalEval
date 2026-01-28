Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg : add_spec (-999998) (-10) (-1000008).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.