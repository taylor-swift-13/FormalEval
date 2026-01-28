Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_1684168416842_98765432102 : gcd_spec 1684168416842 98765432102 2.
Proof.
  unfold gcd_spec.
  split.
  - replace 2 with (Z.gcd 1684168416842 98765432102) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.