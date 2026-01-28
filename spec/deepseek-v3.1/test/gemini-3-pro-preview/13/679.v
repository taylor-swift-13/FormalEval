Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_18_192 : gcd_spec 18 192 6.
Proof.
  unfold gcd_spec.
  split.
  - replace 6 with (Z.gcd 18 192) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.