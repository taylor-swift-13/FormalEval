Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_969_969 : gcd_spec 969 969 969.
Proof.
  unfold gcd_spec.
  split.
  - replace 969 with (Z.gcd 969 969) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.