Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec 3 6789 27.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  (* The goal becomes: 27 = Z.abs (3 mod 10) * Z.abs (6789 mod 10) *)
  (* 3 mod 10 = 3, 6789 mod 10 = 9, 3 * 9 = 27 *)
  reflexivity.
Qed.