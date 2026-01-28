Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg97_10001 : add_spec (-97) 10001 9904.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.