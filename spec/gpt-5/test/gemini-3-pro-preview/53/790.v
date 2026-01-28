Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg103_neg103 : add_spec (-103) (-103) (-206).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.