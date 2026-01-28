Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1234567890_1684168416841 : gcd_spec 1234567890 1684168416841 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 1234567890 1684168416841) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.