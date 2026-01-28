Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000_0 : add_spec 1000000 0 1000000.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.