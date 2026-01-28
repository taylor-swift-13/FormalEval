Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-9876543209) (-123458) 72.
Proof.
  unfold multiply_spec.
  (* The goal becomes 72 = ((Z.abs -9876543209) mod 10) * ((Z.abs -123458) mod 10) *)
  (* abs(-9876543209) mod 10 = 9 *)
  (* abs(-123458) mod 10 = 8 *)
  (* 9 * 8 = 72 *)
  reflexivity.
Qed.