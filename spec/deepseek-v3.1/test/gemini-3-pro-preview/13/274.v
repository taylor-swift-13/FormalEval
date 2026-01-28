Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_99999999_99999999 : gcd_spec 99999999 99999999 99999999.
Proof.
  unfold gcd_spec.
  split.
  - replace 99999999 with (Z.gcd 99999999 99999999) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.