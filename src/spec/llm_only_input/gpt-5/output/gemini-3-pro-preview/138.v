Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example is_equal_to_sum_even_spec_test_4_false :
  is_equal_to_sum_even_spec 4%Z false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [Hge Hmod].
    exfalso.
    assert (4 < 8)%Z by lia.
    lia.
Qed.