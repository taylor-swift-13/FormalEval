Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_659_191 : add_spec 659 191 850.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.