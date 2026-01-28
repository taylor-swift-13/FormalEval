Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1684168416846_1684168416846 : gcd_spec 1684168416846 1684168416846 1684168416846.
Proof.
  unfold gcd_spec.
  split.
  - replace 1684168416846 with (Z.gcd 1684168416846 1684168416846) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.