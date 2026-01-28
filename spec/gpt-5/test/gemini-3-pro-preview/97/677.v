Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 1234567890 1092387464 0.
Proof.
  unfold multiply_spec.
  (* The goal becomes 0 = ((Z.abs 1234567890) mod 10) * ((Z.abs 1092387464) mod 10) *)
  (* 1234567890 mod 10 = 0 *)
  (* 1092387464 mod 10 = 4 *)
  (* 0 * 4 = 0 *)
  reflexivity.
Qed.