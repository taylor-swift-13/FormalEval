Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_269_347 : add_spec 269 347 616.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.