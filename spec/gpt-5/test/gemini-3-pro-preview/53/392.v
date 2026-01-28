Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_9998_1000000000000000000000 : add_spec 9998 1000000000000000000000 1000000000000000009998.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.