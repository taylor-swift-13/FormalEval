Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-17) (-17) 49.
Proof.
  unfold multiply_spec.
  (* The goal becomes 49 = ((Z.abs -17) mod 10) * ((Z.abs -17) mod 10) *)
  (* |-17| mod 10 = 17 mod 10 = 7 *)
  (* |-17| mod 10 = 17 mod 10 = 7 *)
  (* 7 * 7 = 49 *)
  reflexivity.
Qed.