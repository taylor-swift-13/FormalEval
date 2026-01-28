Require Import Coq.ZArith.ZArith.

Definition is_equal_to_sum_even_spec (n : Z) : Prop :=
  (n >= 8)%Z /\ Z.even n = true.

Example test_case_neg_86 : ~ is_equal_to_sum_even_spec (-86)%Z.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [H _].
  compute in H.
  apply H.
  reflexivity.
Qed.