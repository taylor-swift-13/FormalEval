Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_966_3699634 : greatest_common_divisor_spec 966 3699634 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.