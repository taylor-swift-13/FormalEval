Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_12_54 : gcd_spec 12 54 6.
Proof.
  unfold gcd_spec.
  split.
  - replace 6 with (Z.gcd 12 54) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.