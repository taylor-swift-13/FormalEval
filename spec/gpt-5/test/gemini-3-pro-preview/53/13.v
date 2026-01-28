Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_671_705 : add_spec 671 705 1376.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.