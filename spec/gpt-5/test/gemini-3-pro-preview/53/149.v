Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_10000_10000 : add_spec 10000 10000 20000.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.