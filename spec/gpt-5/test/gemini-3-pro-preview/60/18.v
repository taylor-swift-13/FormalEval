Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n_16 : sum_to_n_spec 16%Z 136%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.