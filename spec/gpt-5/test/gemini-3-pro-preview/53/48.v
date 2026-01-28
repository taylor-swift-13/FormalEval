Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_35_753 : add_spec 35 753 788.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.