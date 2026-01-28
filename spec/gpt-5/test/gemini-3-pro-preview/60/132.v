Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n : sum_to_n_spec 1000003%Z 500003500006%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.