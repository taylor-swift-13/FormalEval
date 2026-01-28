Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_300_77 : add_spec 300 77 377.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.