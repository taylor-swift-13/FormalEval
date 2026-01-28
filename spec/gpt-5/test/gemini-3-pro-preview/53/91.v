Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x : Z) (y : Z) (r : Z) : Prop :=
  r = x + y.

Example test_add_950_85 : add_spec 950 85 1035.
Proof.
  unfold add_spec.
  reflexivity.
Qed.