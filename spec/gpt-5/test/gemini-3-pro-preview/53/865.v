Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_97_1 : add_spec 97 1 98.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.