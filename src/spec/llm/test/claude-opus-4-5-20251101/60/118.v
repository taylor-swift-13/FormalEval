Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_999999 : sum_to_n_spec 999999 499999500000.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.