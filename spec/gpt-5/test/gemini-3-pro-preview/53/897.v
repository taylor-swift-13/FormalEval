Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg3_1000001 : add_spec (-3) 1000001 999998.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.