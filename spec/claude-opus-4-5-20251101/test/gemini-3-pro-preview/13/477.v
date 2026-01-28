Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_107_107 : greatest_common_divisor_spec 107 107 107.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.