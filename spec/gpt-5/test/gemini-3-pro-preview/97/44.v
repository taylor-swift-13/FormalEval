Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-12) (-12) 4.
Proof.
  unfold multiply_spec.
  (* The goal becomes 4 = ((Z.abs -12) mod 10) * ((Z.abs -12) mod 10) *)
  (* 12 mod 10 = 2 *)
  (* 2 * 2 = 4 *)
  reflexivity.
Qed.