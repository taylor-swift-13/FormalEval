Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 180%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (H1: x <= 5 \/ x >= 6) by lia.
    assert (H2: x >= -5 \/ x <= -6) by lia.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    + assert (Hrange: -5 <= x <= 5) by lia.
      assert (x = -5 \/ x = -4 \/ x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5) by lia.
      destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]; subst x; simpl in Hx; discriminate Hx.
    + lia.
    + lia.
    + assert (x >= 6 \/ x <= -6) by lia.
      destruct H as [H|H].
      * assert (x * x * x >= 216) by nia.
        lia.
      * assert (x * x * x <= -216) by nia.
        lia.
Qed.