Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 9876543210 (-12344) 0.
Proof.
  unfold multiply_spec.
  (* The goal becomes 0 = ((Z.abs 9876543210) mod 10) * ((Z.abs -12344) mod 10) *)
  (* 9876543210 mod 10 = 0 *)
  (* 12344 mod 10 = 4 *)
  (* 0 * 4 = 0 *)
  reflexivity.
Qed.