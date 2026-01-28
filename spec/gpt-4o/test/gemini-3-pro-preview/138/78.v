Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) : Prop :=
  n >= 8 /\ Z.even n = true.

Example test_case_neg49 : ~ is_equal_to_sum_even_spec (-49).
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [H _].
  unfold Z.ge in H.
  compute in H.
  apply H.
  reflexivity.
Qed.