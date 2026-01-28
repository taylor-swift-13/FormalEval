Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 120%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= 4 /\ x >= -4 \/ x > 4 \/ x < -4) as Hcases by lia.
    destruct Hcases as [[Hle Hge] | [Hgt | Hlt]].
    + assert (x = -4 \/ x = -3 \/ x = -2 \/ x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) as Hvals by lia.
      destruct Hvals as [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]];
      rewrite H in Hx; simpl in Hx; lia.
    + assert (x * x * x >= 5 * 5 * 5) as Hbound.
      { assert (x >= 5) by lia.
        assert (x * x >= 25) by nia.
        nia. }
      lia.
    + assert (x * x * x <= (-5) * (-5) * (-5)) as Hbound.
      { assert (x <= -5) by lia.
        nia. }
      lia.
Qed.