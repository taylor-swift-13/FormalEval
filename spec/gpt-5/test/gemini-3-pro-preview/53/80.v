Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_502_653 : add_spec 502 653 1155.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.