Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (res : Z) : Prop :=
  res = (n * (n + 1)) / 2.

Example sum_to_499992_test : sum_to_n_spec 499992 124996250028.
Proof.
  unfold sum_to_n_spec.
  (* Compute (499992 * (499992 + 1)) / 2 *)
  simpl.
  reflexivity.
Qed.