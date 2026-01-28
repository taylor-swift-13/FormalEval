Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_49_49 : gcd_spec 49 49 49.
Proof.
  unfold gcd_spec.
  split.
  - replace 49 with (Z.gcd 49 49) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.