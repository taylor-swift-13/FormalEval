Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-16) 5 30.
Proof.
  unfold multiply_spec.
  (* The goal becomes 30 = ((Z.abs -16) mod 10) * ((Z.abs 5) mod 10) *)
  (* 16 mod 10 = 6 *)
  (* 5 mod 10 = 5 *)
  (* 6 * 5 = 30 *)
  reflexivity.
Qed.