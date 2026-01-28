Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_123456790_1684168416838 : gcd_spec 123456790 1684168416838 2.
Proof.
  unfold gcd_spec.
  split.
  - replace 2 with (Z.gcd 123456790 1684168416838) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.