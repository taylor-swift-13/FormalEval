Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_108_966 : gcd_spec 108 966 6.
Proof.
  unfold gcd_spec.
  split.
  - replace 6 with (Z.gcd 108 966) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.