Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 1 (-16) 6.
Proof.
  unfold multiply_spec.
  (* The goal becomes 6 = ((Z.abs 1) mod 10) * ((Z.abs -16) mod 10) *)
  (* 1 mod 10 = 1 *)
  (* 16 mod 10 = 6 *)
  (* 1 * 6 = 6 *)
  reflexivity.
Qed.