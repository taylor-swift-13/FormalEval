Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) : Prop :=
  n >= 8 /\ Z.even n = true.

Example test_case_neg_91 : ~ is_equal_to_sum_even_spec (-91).
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge Heven].
  compute in Hge.
  apply Hge.
  reflexivity.
Qed.