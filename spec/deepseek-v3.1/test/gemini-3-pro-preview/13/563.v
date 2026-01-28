Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1684168416841_1684168416841 : gcd_spec 1684168416841 1684168416841 1684168416841.
Proof.
  unfold gcd_spec.
  split.
  - replace 1684168416841 with (Z.gcd 1684168416841 1684168416841) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.