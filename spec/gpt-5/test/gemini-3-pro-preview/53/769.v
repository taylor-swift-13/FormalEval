Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg96_neg97 : add_spec (-96) (-97) (-193).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.