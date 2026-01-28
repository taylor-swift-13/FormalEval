Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_49_14 : gcd_spec 49 14 7.
Proof.
  unfold gcd_spec.
  split.
  - replace 7 with (Z.gcd 49 14) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.