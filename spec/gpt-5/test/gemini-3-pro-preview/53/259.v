Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000000000000000_1000 : add_spec 1000000000000000000 1000 1000000000000001000.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.