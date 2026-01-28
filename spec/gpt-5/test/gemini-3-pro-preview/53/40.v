Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_571_697 : add_spec 571 697 1268.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.