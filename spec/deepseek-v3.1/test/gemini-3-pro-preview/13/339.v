Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_999999998_999999998 : gcd_spec 999999998 999999998 999999998.
Proof.
  unfold gcd_spec.
  split.
  - replace 999999998 with (Z.gcd 999999998 999999998) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.