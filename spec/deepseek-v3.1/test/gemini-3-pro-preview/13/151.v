Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_193_193 : gcd_spec 193 193 193.
Proof.
  unfold gcd_spec.
  split.
  - replace 193 with (Z.gcd 193 193) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.