Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_2516980251698_111111110 : gcd_spec 2516980251698 111111110 22.
Proof.
  unfold gcd_spec.
  split.
  - replace 22 with (Z.gcd 2516980251698 111111110) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.