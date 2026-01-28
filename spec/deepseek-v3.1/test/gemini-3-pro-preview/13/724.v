Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1000000000_965 : gcd_spec 1000000000 965 5.
Proof.
  unfold gcd_spec.
  split.
  - replace 5 with (Z.gcd 1000000000 965) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.