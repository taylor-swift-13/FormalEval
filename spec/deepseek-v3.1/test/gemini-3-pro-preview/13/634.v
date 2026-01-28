Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_108_987654320 : gcd_spec 108 987654320 4.
Proof.
  unfold gcd_spec.
  split.
  - replace 4 with (Z.gcd 108 987654320) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.