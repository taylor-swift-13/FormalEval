Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111109_3699638 : greatest_common_divisor_spec 111111109 3699638 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.