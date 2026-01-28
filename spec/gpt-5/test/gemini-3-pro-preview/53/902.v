Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg96_neg999998 : add_spec (-96) (-999998) (-1000094).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.