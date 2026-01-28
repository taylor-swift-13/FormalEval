Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec (-1000001)%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= -101 \/ x = -100 \/ (-99 <= x <= 99) \/ x = 100 \/ x >= 101) as Hcases by lia.
    destruct Hcases as [H1 | [H1 | [H1 | [H1 | H1]]]].
    + assert (x * x * x <= -101 * -101 * -101) by nia.
      assert (-101 * -101 * -101 = -1030301) by reflexivity.
      lia.
    + rewrite H1 in Hx.
      simpl in Hx.
      lia.
    + assert (x * x * x >= -99 * 99 * 99) by nia.
      assert (x * x * x <= 99 * 99 * 99) by nia.
      assert (99 * 99 * 99 = 970299) by reflexivity.
      assert (-99 * 99 * 99 = -970299) by reflexivity.
      lia.
    + rewrite H1 in Hx.
      simpl in Hx.
      lia.
    + assert (x * x * x >= 101 * 101 * 101) by nia.
      assert (101 * 101 * 101 = 1030301) by reflexivity.
      lia.
Qed.