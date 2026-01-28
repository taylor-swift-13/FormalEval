Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-12) 1092387465 10.
Proof.
  unfold multiply_spec.
  (* The goal becomes 10 = ((Z.abs -12) mod 10) * ((Z.abs 1092387465) mod 10) *)
  (* -12 abs -> 12 mod 10 = 2 *)
  (* 1092387465 mod 10 = 5 *)
  (* 2 * 5 = 10 *)
  reflexivity.
Qed.