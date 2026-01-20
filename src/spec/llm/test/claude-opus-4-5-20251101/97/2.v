Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply : multiply_spec 19%Z 28%Z 72%Z.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  simpl.
  reflexivity.
Qed.