Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_2516980251699_2516980251699 : greatest_common_divisor_spec 2516980251699 2516980251699 2516980251699.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.