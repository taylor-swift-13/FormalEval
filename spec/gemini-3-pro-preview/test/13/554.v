Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654324_968 : greatest_common_divisor_spec 987654324 968 4.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.