Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_neg_999999_999999999999999999999 : add_spec (-999999) 999999999999999999999 999999999999999000000.
Proof.
  unfold add_spec.
  reflexivity.
Qed.