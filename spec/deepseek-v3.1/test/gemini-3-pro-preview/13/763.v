Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_109_123456789 : gcd_spec 109 123456789 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 109 123456789) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.