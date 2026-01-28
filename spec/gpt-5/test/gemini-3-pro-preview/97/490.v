Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-12348) (-16) 48.
Proof.
  unfold multiply_spec.
  (* The goal becomes 48 = ((Z.abs -12348) mod 10) * ((Z.abs -16) mod 10) *)
  (* 12348 mod 10 = 8 *)
  (* 16 mod 10 = 6 *)
  (* 8 * 6 = 48 *)
  reflexivity.
Qed.