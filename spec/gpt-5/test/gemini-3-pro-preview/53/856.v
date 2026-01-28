Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000000000000000_neg12 : add_spec 1000000000000000000 (-12) 999999999999999988.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.