Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_98765432101_987654318 : gcd_spec 98765432101 987654318 7.
Proof.
  unfold gcd_spec.
  split.
  - replace 7 with (Z.gcd 98765432101 987654318) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.