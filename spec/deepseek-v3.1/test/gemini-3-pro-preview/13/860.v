Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_50_234567890 : gcd_spec 50 234567890 10.
Proof.
  unfold gcd_spec.
  split.
  - replace 10 with (Z.gcd 50 234567890) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.