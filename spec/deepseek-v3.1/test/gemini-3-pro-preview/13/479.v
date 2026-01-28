Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_234567892_234567892 : gcd_spec 234567892 234567892 234567892.
Proof.
  unfold gcd_spec.
  split.
  - replace 234567892 with (Z.gcd 234567892 234567892) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.