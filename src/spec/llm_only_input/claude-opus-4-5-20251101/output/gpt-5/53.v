Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example add_test_case : add_spec 0%Z 1%Z 1%Z.
Proof.
  unfold add_spec.
  reflexivity.
Qed.