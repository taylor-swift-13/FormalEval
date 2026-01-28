Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg999999_neg10000 : add_spec (-999999) (-10000) (-1009999).
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.