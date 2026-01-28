Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-87) 321 7.
Proof.
  unfold multiply_spec.
  (* The goal becomes 7 = ((Z.abs -87) mod 10) * ((Z.abs 321) mod 10) *)
  (* 87 mod 10 = 7 *)
  (* 321 mod 10 = 1 *)
  (* 7 * 1 = 7 *)
  reflexivity.
Qed.