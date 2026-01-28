Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg10001_70 : add_spec (-10001) 70 (-9931).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.