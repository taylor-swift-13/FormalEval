Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_966_111111112 : gcd_spec 966 111111112 14.
Proof.
  unfold gcd_spec.
  split.
  - replace 14 with (Z.gcd 966 111111112) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.