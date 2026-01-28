Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-123457) 2 14.
Proof.
  unfold multiply_spec.
  (* The goal becomes 14 = ((Z.abs -123457) mod 10) * ((Z.abs 2) mod 10) *)
  (* 123457 mod 10 = 7 *)
  (* 2 mod 10 = 2 *)
  (* 7 * 2 = 14 *)
  reflexivity.
Qed.