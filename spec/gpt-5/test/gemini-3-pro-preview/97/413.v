Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-11) 9876543209 9.
Proof.
  unfold multiply_spec.
  (* The goal becomes 9 = ((Z.abs -11) mod 10) * ((Z.abs 9876543209) mod 10) *)
  (* abs(-11) mod 10 = 1 *)
  (* 9876543209 mod 10 = 9 *)
  (* 1 * 9 = 9 *)
  reflexivity.
Qed.