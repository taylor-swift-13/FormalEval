Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_969_969 : greatest_common_divisor_spec 969 969 969.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.