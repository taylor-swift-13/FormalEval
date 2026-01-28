Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_473_231 : add_spec 473 231 704.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.