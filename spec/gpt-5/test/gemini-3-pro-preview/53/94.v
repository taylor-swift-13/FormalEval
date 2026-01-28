Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_994_169 : add_spec 994 169 1163.
Proof.
  unfold add_spec.
  reflexivity.
Qed.