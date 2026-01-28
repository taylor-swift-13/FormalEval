Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_483_198 : add_spec 483 198 681.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.