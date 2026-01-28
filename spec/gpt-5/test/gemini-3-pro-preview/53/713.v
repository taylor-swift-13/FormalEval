Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000001_neg2 : add_spec 1000001 (-2) 999999.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.