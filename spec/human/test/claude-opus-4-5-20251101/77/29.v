Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

Example test_iscube_2 : problem_77_spec 26%Z false.
Proof.
  unfold problem_77_spec.
  split.
  - intros H.
    discriminate H.
  - intros [x Hx].
    exfalso.
    assert (x <= 2 \/ x >= 3) as Hcase by lia.
    assert (x >= -2 \/ x <= -3) as Hcase2 by lia.
    destruct (Z.eq_dec x 0) as [H0|H0].
    + subst x. simpl in Hx. lia.
    + destruct (Z.eq_dec x 1) as [H1|H1].
      * subst x. simpl in Hx. lia.
      * destruct (Z.eq_dec x 2) as [H2|H2].
        -- subst x. simpl in Hx. lia.
        -- destruct (Z.eq_dec x (-1)) as [Hm1|Hm1].
           ++ subst x. simpl in Hx. lia.
           ++ destruct (Z.eq_dec x (-2)) as [Hm2|Hm2].
              ** subst x. simpl in Hx. lia.
              ** assert (x >= 3 \/ x <= -3) as Hbig by lia.
                 destruct Hbig as [Hpos|Hneg].
                 --- assert (x * x * x >= 27) by nia. lia.
                 --- assert (x * x * x <= -27) by nia. lia.
Qed.