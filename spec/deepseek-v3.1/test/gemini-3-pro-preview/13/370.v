Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_999999999_12 : gcd_spec 999999999 12 3.
Proof.
  unfold gcd_spec.
  split.
  - replace 3 with (Z.gcd 999999999 12) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.