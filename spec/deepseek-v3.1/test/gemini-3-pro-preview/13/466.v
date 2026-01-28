Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_418_987654324 : gcd_spec 418 987654324 2.
Proof.
  unfold gcd_spec.
  split.
  - replace 2 with (Z.gcd 418 987654324) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.