Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_826_822 : add_spec 826 822 1648.
Proof.
  unfold add_spec.
  reflexivity.
Qed.