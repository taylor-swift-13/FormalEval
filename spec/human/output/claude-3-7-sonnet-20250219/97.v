Require Import ZArith.
Open Scope Z_scope.

Definition problem_97_spec (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example test_multiply_148_412 :
  problem_97_spec 148 412 16.
Proof.
  unfold problem_97_spec.
  (* Compute absolute values and mods *)
  simpl.
  (* Z.abs 148 = 148, 148 mod 10 = 8 *)
  (* Z.abs 412 = 412, 412 mod 10 = 2 *)
  (* 8 * 2 = 16 *)
  reflexivity.
Qed.