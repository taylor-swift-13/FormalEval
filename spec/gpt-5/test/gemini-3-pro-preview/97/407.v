Require Import ZArith.

Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example test_multiply_spec : multiply_spec (-12346) 987654 24.
Proof.
  unfold multiply_spec.
  (* The goal becomes 24 = ((Z.abs -12346) mod 10) * ((Z.abs 987654) mod 10) *)
  (* 12346 mod 10 = 6 *)
  (* 987654 mod 10 = 4 *)
  (* 6 * 4 = 24 *)
  reflexivity.
Qed.