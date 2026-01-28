Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1000000001_1000000002 : gcd_spec 1000000001 1000000002 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 1000000001 1000000002) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.