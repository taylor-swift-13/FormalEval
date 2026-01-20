Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699638_123456788 : greatest_common_divisor_spec 3699638 123456788 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.