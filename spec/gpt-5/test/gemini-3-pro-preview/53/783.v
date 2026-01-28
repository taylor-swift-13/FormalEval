Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg : add_spec (-999999) (-1000000) (-1999999).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.