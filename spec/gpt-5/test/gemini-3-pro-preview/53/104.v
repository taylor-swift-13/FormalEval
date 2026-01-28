Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_550_501 : add_spec 550 501 1051.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.