Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_100_9 : gcd_spec 100 9 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 100 9) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.