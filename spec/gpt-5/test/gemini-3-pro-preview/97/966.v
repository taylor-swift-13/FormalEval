Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 4 1092387467 28.
Proof.
  unfold multiply_spec.
  (* The goal becomes 28 = ((Z.abs 4) mod 10) * ((Z.abs 1092387467) mod 10) *)
  (* 4 mod 10 = 4 *)
  (* 1092387467 mod 10 = 7 *)
  (* 4 * 7 = 28 *)
  reflexivity.
Qed.