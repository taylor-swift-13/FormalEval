Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_968_1684168416845 : greatest_common_divisor_spec 968 1684168416845 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.