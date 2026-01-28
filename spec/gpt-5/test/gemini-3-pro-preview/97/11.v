Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 39 25 45.
Proof.
  unfold multiply_spec.
  (* The goal becomes 45 = ((Z.abs 39) mod 10) * ((Z.abs 25) mod 10) *)
  (* 39 mod 10 = 9 *)
  (* 25 mod 10 = 5 *)
  (* 9 * 5 = 45 *)
  reflexivity.
Qed.