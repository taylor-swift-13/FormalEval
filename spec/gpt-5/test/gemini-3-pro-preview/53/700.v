Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg103_1000 : add_spec (-103) 1000 897.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.