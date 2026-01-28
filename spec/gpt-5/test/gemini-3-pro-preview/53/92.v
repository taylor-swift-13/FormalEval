Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_223_50 : add_spec 223 50 273.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.