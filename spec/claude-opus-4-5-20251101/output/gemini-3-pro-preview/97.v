Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec 148 412 16.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  (* The goal becomes: 16 = Z.abs (148 mod 10) * Z.abs (412 mod 10) *)
  (* 148 mod 10 = 8, 412 mod 10 = 2, 8 * 2 = 16 *)
  reflexivity.
Qed.