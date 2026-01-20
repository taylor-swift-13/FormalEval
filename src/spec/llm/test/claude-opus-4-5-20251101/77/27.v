Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 123%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H. discriminate H.
  - intros [n Hn].
    exfalso.
    assert (n <= 4 /\ n >= -4 -> n * n * n <> 123).
    {
      intros [Hle Hge].
      assert (n = -4 \/ n = -3 \/ n = -2 \/ n = -1 \/ n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4) by lia.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]; rewrite H; lia.
    }
    assert (n >= 5 -> n * n * n >= 125).
    {
      intros Hge.
      assert (n * n >= 25). { assert (n * n >= 5 * 5) by nia. lia. }
      assert (n * n * n >= 25 * 5) by nia. lia.
    }
    assert (n <= -5 -> n * n * n <= -125).
    {
      intros Hle.
      assert (n * n >= 25). { assert ((-n) * (-n) >= 5 * 5) by nia. lia. }
      assert (n * n * n <= -125) by nia. lia.
    }
    assert (n * n * n = 123 -> False).
    {
      intros Heq.
      destruct (Z.le_gt_cases n 4) as [Hle4|Hgt4].
      - destruct (Z.le_gt_cases (-4) n) as [Hge4|Hlt4].
        + apply H in Heq; [assumption | lia].
        + assert (n <= -5) by lia. apply H1 in H2. lia.
      - assert (n >= 5) by lia. apply H0 in H2. lia.
    }
    apply H2. exact Hn.
Qed.