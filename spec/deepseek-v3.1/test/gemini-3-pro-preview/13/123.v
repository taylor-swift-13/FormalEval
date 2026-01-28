Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_123456789_999999999 : gcd_spec 123456789 999999999 9.
Proof.
  unfold gcd_spec.
  split.
  - replace 9 with (Z.gcd 123456789 999999999) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.