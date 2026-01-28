Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1001_1002 : add_spec 1001 1002 2003.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.