Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_2516980251697_1684168416843 : greatest_common_divisor_spec 2516980251697 1684168416843 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.