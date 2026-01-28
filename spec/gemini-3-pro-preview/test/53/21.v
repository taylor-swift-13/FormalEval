Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_705_148: add_spec 705 148 853.
Proof.
  unfold add_spec.
  reflexivity.
Qed.