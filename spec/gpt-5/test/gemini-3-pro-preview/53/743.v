Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_69_70 : add_spec 69 70 139.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.