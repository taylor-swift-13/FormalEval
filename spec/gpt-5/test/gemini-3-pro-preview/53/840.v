Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_69_69 : add_spec 69 69 138.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.