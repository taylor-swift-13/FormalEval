Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n_2 : sum_to_n_spec 499999%Z 124999750000%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.