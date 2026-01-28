Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_111111112_111111112 : gcd_spec 111111112 111111112 111111112.
Proof.
  unfold gcd_spec.
  split.
  - replace 111111112 with (Z.gcd 111111112 111111112) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.