Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_987654324_987654323 : gcd_spec 987654324 987654323 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 987654324 987654323) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.