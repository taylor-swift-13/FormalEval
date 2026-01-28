Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec 2938475611 6787 7.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  reflexivity.
Qed.