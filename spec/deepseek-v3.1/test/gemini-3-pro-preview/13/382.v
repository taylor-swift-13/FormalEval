Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1234567890_1234567890 : gcd_spec 1234567890 1234567890 1234567890.
Proof.
  unfold gcd_spec.
  split.
  - replace 1234567890 with (Z.gcd 1234567890 1234567890) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.