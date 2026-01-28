Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n_499992 : sum_to_n_spec 499992%Z 124996250028%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.