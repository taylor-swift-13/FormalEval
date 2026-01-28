Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_81_81 : gcd_spec 81 81 81.
Proof.
  unfold gcd_spec.
  split.
  - replace 81 with (Z.gcd 81 81) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.