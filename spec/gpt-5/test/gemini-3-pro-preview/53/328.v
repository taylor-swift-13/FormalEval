Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10002_5 : add_spec 10002 5 10007.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.