Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_54_33 : gcd_spec 54 33 3.
Proof.
  unfold gcd_spec.
  split.
  - replace 3 with (Z.gcd 54 33) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.