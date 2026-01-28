Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec 1 6790 0.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  (* The goal becomes: 0 = Z.abs (1 mod 10) * Z.abs (6790 mod 10) *)
  (* 1 mod 10 = 1, 6790 mod 10 = 0, 1 * 0 = 0 *)
  reflexivity.
Qed.