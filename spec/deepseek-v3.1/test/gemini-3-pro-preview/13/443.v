Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_234567891_234567891 : gcd_spec 234567891 234567891 234567891.
Proof.
  unfold gcd_spec.
  split.
  - replace 234567891 with (Z.gcd 234567891 234567891) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.