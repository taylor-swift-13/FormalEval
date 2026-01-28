Require Import Coq.ZArith.ZArith.

Definition is_equal_to_sum_even_spec (n : Z) : Prop :=
  (n >= 8)%Z /\ Z.even n = true.

Example test_case_neg25 : ~ is_equal_to_sum_even_spec (-25)%Z.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge _].
  compute in Hge.
  contradiction.
Qed.