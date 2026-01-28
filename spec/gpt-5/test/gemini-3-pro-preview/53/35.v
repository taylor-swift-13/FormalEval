Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_666_55 : add_spec 666 55 721.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.