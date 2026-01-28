Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_144_60 : gcd_spec 144 60 12.
Proof.
  unfold gcd_spec.
  split.
  - replace 12 with (Z.gcd 144 60) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.