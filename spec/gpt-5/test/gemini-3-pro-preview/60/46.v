Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n : sum_to_n_spec 56%Z 1596%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.