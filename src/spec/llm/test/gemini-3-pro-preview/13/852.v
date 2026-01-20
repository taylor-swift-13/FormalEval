Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_968_966 : greatest_common_divisor_spec 968 966 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.