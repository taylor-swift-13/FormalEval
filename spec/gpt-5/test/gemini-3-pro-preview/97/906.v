Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec 3 246813580 0.
Proof.
  unfold multiply_spec.
  (* The goal becomes 0 = ((Z.abs 3) mod 10) * ((Z.abs 246813580) mod 10) *)
  (* 3 mod 10 = 3 *)
  (* 246813580 mod 10 = 0 *)
  (* 3 * 0 = 0 *)
  reflexivity.
Qed.