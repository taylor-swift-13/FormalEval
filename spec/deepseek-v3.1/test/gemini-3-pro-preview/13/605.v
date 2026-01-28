Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_2147483647_2147483647 : gcd_spec 2147483647 2147483647 2147483647.
Proof.
  unfold gcd_spec.
  split.
  - replace 2147483647 with (Z.gcd 2147483647 2147483647) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.