Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_8_10000 : add_spec 8 10000 10008.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.