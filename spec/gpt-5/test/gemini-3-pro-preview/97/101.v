Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-5) (-3) 15.
Proof.
  unfold multiply_spec.
  (* The goal becomes 15 = ((Z.abs -5) mod 10) * ((Z.abs -3) mod 10) *)
  (* 5 mod 10 = 5 *)
  (* 3 mod 10 = 3 *)
  (* 5 * 3 = 15 *)
  reflexivity.
Qed.