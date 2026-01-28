Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_69_99: add_spec 69 99 168.
Proof.
  unfold add_spec.
  reflexivity.
Qed.