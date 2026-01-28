Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_192_99999999 : gcd_spec 192 99999999 3.
Proof.
  unfold gcd_spec.
  split.
  - replace 3 with (Z.gcd 192 99999999) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.