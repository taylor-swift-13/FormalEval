Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 730%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (H1: x <= 8 \/ x >= 10 \/ x = 9) by lia.
    assert (H2: x >= -8 \/ x <= -10 \/ x = -9) by lia.
    destruct H1 as [H1 | [H1 | H1]].
    + destruct H2 as [H2 | [H2 | H2]].
      * assert (Hbound: -8 <= x <= 8) by lia.
        assert (x = -8 \/ x = -7 \/ x = -6 \/ x = -5 \/ x = -4 \/ x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8) by lia.
        destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]; subst x; simpl in Hx; lia.
      * assert (x <= -10) by lia.
        assert (x * x * x <= -1000) by nia.
        lia.
      * subst x. simpl in Hx. lia.
    + assert (x >= 10) by lia.
      assert (x * x * x >= 1000) by nia.
      lia.
    + subst x. simpl in Hx. lia.
Qed.