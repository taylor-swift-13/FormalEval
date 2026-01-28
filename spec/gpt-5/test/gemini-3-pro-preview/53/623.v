Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg97_neg1000000 : add_spec (-97) (-1000000) (-1000097).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.