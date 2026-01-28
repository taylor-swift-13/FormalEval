Require Import ZArith.
Require Import Coq.ZArith.Zabs.

Open Scope Z_scope.

Definition unit_digit (n : Z) : Z :=
  Z.abs (n mod 10).

Definition multiply_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = (unit_digit a) * (unit_digit b).

Example test_multiply_spec : multiply_spec (-123456) (-12344) 24.
Proof.
  unfold multiply_spec.
  unfold unit_digit.
  (* The goal becomes: 24 = Z.abs (-123456 mod 10) * Z.abs (-12344 mod 10) *)
  (* -123456 mod 10 = 4, -12344 mod 10 = 6, 4 * 6 = 24 *)
  reflexivity.
Qed.