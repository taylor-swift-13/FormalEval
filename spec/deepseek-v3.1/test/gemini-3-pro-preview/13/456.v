Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_3699639_3699639 : gcd_spec 3699639 3699639 3699639.
Proof.
  unfold gcd_spec.
  split.
  - replace 3699639 with (Z.gcd 3699639 3699639) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.