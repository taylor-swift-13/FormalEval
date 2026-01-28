Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_265_822 : add_spec 265 822 1087.
Proof.
  unfold add_spec.
  simpl.
  reflexivity.
Qed.