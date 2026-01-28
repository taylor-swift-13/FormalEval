Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg101_3: add_spec (-101) 3 (-98).
Proof.
  unfold add_spec.
  reflexivity.
Qed.