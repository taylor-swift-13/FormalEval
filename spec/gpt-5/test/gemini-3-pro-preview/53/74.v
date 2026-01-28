Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_125_119 : add_spec 125 119 244.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.