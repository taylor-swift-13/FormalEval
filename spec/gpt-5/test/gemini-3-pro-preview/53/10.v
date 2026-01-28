Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_911_703 : add_spec 911 703 1614.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.