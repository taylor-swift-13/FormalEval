Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 510%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (H7: 7 * 7 * 7 = 343) by reflexivity.
    assert (H8: 8 * 8 * 8 = 512) by reflexivity.
    assert (Hneg8: (-8) * (-8) * (-8) = -512) by reflexivity.
    assert (Hneg7: (-7) * (-7) * (-7) = -343) by reflexivity.
    destruct (Z.lt_trichotomy x 0) as [Hneg | [Hzero | Hpos]].
    + destruct (Z.lt_trichotomy x (-8)) as [Hlt | [Heq | Hgt]].
      * assert (x <= -9) by lia.
        assert (x * x * x <= -729) by nia.
        lia.
      * rewrite Heq in Hx. lia.
      * assert (-7 <= x <= -1) by lia.
        assert (-343 <= x * x * x <= -1) by nia.
        lia.
    + rewrite Hzero in Hx. simpl in Hx. lia.
    + destruct (Z.lt_trichotomy x 8) as [Hlt | [Heq | Hgt]].
      * assert (1 <= x <= 7) by lia.
        assert (1 <= x * x * x <= 343) by nia.
        lia.
      * rewrite Heq in Hx. lia.
      * assert (x >= 9) by lia.
        assert (x * x * x >= 729) by nia.
        lia.
Qed.