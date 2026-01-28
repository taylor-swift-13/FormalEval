Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_6_1000000000000000000 : add_spec 6 1000000000000000000 1000000000000000006.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.