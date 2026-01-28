Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_965_964 : gcd_spec 965 964 1.
Proof.
  unfold gcd_spec.
  split.
  - replace 1 with (Z.gcd 965 964) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.