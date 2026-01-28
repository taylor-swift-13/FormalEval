Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_81_24 : gcd_spec 81 24 3.
Proof.
  unfold gcd_spec.
  split.
  - replace 3 with (Z.gcd 81 24) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.