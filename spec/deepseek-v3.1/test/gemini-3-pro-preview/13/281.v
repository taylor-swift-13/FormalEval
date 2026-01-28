Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_234567887_123456788 : gcd_spec 234567887 123456788 17.
Proof.
  unfold gcd_spec.
  split.
  - replace 17 with (Z.gcd 234567887 123456788) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.