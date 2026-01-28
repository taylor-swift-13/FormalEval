Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_528_830 : add_spec 528 830 1358.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.