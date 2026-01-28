Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (sum : Z) : Prop :=
  sum = ((n + 1) * n) / 2.

Example test_sum_to_n_532177 : sum_to_n_spec 532177%Z 141606445753%Z.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.