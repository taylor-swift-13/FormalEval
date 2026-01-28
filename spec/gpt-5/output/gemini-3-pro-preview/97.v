Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 148 412 16.
Proof.
  unfold multiply_spec.
  (* The goal becomes 16 = ((Z.abs 148) mod 10) * ((Z.abs 412) mod 10) *)
  (* 148 mod 10 = 8 *)
  (* 412 mod 10 = 2 *)
  (* 8 * 2 = 16 *)
  reflexivity.
Qed.