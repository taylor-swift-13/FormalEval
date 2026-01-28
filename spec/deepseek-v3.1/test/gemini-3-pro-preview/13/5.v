Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_100_50 : gcd_spec 100 50 50.
Proof.
  unfold gcd_spec.
  split.
  - replace 50 with (Z.gcd 100 50) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.