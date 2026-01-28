Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_190_190 : gcd_spec 190 190 190.
Proof.
  unfold gcd_spec.
  split.
  - replace 190 with (Z.gcd 190 190) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.