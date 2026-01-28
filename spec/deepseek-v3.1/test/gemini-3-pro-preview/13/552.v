Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_968_968 : gcd_spec 968 968 968.
Proof.
  unfold gcd_spec.
  split.
  - replace 968 with (Z.gcd 968 968) by reflexivity.
    apply Zgcd_is_gcd.
  - lia.
Qed.