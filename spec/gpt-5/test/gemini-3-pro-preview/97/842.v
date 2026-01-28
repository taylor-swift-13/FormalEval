Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 31 2 2.
Proof.
  unfold multiply_spec.
  (* The goal becomes 2 = ((Z.abs 31) mod 10) * ((Z.abs 2) mod 10) *)
  (* 31 mod 10 = 1 *)
  (* 2 mod 10 = 2 *)
  (* 1 * 2 = 2 *)
  reflexivity.
Qed.