Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_3699635_3699635 : gcd_spec 3699635 3699635 3699635.
Proof.
  unfold gcd_spec.
  split.
  - replace 3699635 with (Z.gcd 3699635 3699635) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.