Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_97_96 : add_spec 97 96 193.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.