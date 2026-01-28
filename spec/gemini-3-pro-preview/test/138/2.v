Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 6 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    destruct H as [Hge8 Hmod].
    lia.
Qed.