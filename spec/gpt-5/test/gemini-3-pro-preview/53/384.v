Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_1000000000000000000_5 : add_spec 1000000000000000000 5 1000000000000000005.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.