Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699639_966 : greatest_common_divisor_spec 3699639 966 3.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.