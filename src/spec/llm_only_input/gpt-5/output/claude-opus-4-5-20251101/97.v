Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_case : multiply_spec 148%Z 412%Z 16%Z.
Proof.
  unfold multiply_spec, unit_digit.
  compute.
  reflexivity.
Qed.