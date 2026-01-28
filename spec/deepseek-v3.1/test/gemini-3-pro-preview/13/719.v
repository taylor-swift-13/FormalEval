Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_192_1000000000 : gcd_spec 192 1000000000 64.
Proof.
  unfold gcd_spec.
  split.
  - replace 64 with (Z.gcd 192 1000000000) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.