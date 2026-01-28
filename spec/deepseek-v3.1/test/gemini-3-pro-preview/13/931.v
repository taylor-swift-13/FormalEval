Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_3699640_1684168416840 : gcd_spec 3699640 1684168416840 280.
Proof.
  unfold gcd_spec.
  split.
  - replace 280 with (Z.gcd 3699640 1684168416840) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.