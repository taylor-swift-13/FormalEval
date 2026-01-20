Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111111_98765432100 : greatest_common_divisor_spec 111111111 98765432100 9.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.