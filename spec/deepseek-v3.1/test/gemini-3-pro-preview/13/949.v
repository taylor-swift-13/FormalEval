Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_48_964 : gcd_spec 48 964 4.
Proof.
  unfold gcd_spec.
  split.
  - replace 4 with (Z.gcd 48 964) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.