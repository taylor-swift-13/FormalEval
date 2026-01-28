Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_361_945 : add_spec 361 945 1306.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.