Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_746_105 : add_spec 746 105 851.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.