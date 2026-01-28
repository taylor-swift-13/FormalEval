Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) : Prop :=
  n >= 8 /\ Z.even n = true.

Example test_case_neg_72 : ~ is_equal_to_sum_even_spec (-72).
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge Heven].
  lia.
Qed.