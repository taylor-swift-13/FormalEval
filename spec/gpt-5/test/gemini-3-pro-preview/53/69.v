Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_567_768 : add_spec 567 768 1335.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.