Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_965_965 : gcd_spec 965 965 965.
Proof.
  unfold gcd_spec.
  split.
  - replace 965 with (Z.gcd 965 965) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.