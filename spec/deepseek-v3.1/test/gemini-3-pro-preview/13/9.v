Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_33_55 : gcd_spec 33 55 11.
Proof.
  unfold gcd_spec.
  split.
  - replace 11 with (Z.gcd 33 55) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.