Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_890_180 : add_spec 890 180 1070.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.