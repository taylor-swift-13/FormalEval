Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_98_56 : gcd_spec 98 56 14.
Proof.
  unfold gcd_spec.
  split.
  - replace 14 with (Z.gcd 98 56) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.