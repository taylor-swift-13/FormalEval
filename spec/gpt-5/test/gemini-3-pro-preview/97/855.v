Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 987654 (-8) 32.
Proof.
  unfold multiply_spec.
  (* The goal becomes 32 = ((Z.abs 987654) mod 10) * ((Z.abs -8) mod 10) *)
  (* 987654 mod 10 = 4 *)
  (* 8 mod 10 = 8 *)
  (* 4 * 8 = 32 *)
  reflexivity.
Qed.