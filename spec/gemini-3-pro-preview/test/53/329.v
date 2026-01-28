Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition add_spec (x y result : Z) : Prop :=
  result = x + y.

Example test_add_spec_neg98_bigint: add_spec (-98) 123456789098765432101234567891 123456789098765432101234567793.
Proof.
  unfold add_spec.
  reflexivity.
Qed.