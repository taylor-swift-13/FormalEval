Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec 76 67 42.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  (* The goal becomes: 42 = Z.abs (76 mod 10) * Z.abs (67 mod 10) *)
  (* 76 mod 10 = 6, 67 mod 10 = 7, 6 * 7 = 42 *)
  reflexivity.
Qed.