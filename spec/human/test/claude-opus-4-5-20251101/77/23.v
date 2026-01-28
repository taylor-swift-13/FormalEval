Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 728%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= 8 /\ x >= -8 \/ x > 8 \/ x < -8) as Hcases by lia.
    destruct Hcases as [[Hle Hge] | [Hgt | Hlt]].
    + assert (x = -8 \/ x = -7 \/ x = -6 \/ x = -5 \/ x = -4 \/ x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5 \/ x = 6 \/ x = 7 \/ x = 8) as Hvals by lia.
      destruct Hvals as [H1|[H2|[H3|[H4|[H5|[H6|[H7|[H8|[H9|[H10|[H11|[H12|[H13|[H14|[H15|[H16|H17]]]]]]]]]]]]]]]];
      subst x; simpl in Hx; lia.
    + assert (x * x * x >= 9 * 9 * 9) as Hbound.
      { assert (x >= 9) by lia.
        assert (x * x >= 81) by nia.
        nia. }
      lia.
    + assert (x * x * x <= (-9) * (-9) * (-9)) as Hbound.
      { assert (x <= -9) by lia.
        nia. }
      lia.
Qed.