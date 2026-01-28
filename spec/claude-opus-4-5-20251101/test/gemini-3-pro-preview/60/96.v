Require Import ZArith.
Open Scope Z_scope.

Definition sum_to_n_spec (n : Z) (result : Z) : Prop :=
  result = (n * (n + 1)) / 2.

Example test_sum_to_n_69 : sum_to_n_spec 69 2415.
Proof.
  unfold sum_to_n_spec.
  reflexivity.
Qed.