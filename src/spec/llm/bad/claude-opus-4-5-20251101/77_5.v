Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition iscube_spec (a : Z) (result : bool) : Prop :=
  result = true <-> exists n : Z, n * n * n = a.

Example iscube_test_1 : iscube_spec 180%Z false.
Proof.
  unfold iscube_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    destruct H as [n Hn].
    exfalso.
    assert (n <= 5 \/ n >= 6) as Hcase by lia.
    assert (n >= -5 \/ n <= -6) as Hcase2 by lia.
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    + rewrite Hn0 in Hn. simpl in Hn. lia.
    + destruct (Z.eq_dec n 1) as [Hn1|Hn1].
      * rewrite Hn1 in Hn. simpl in Hn. lia.
      * destruct (Z.eq_dec n 2) as [Hn2|Hn2].
        -- rewrite Hn2 in Hn. simpl in Hn. lia.
        -- destruct (Z.eq_dec n 3) as [Hn3|Hn3].
           ++ rewrite Hn3 in Hn. simpl in Hn. lia.
           ++ destruct (Z.eq_dec n 4) as [Hn4|Hn4].
              ** rewrite Hn4 in Hn. simpl in Hn. lia.
              ** destruct (Z.eq_dec n 5) as [Hn5|Hn5].
                 --- rewrite Hn5 in Hn. simpl in Hn. lia.
                 --- destruct (Z.eq_dec n (-1)) as [Hnm1|Hnm1].
                     +++ rewrite Hnm1 in Hn. simpl in Hn. lia.
                     +++ destruct (Z.eq_dec n (-2)) as [Hnm2|Hnm2].
                         *** rewrite Hnm2 in Hn. simpl in Hn. lia.
                         *** destruct (Z.eq_dec n (-3)) as [Hnm3|Hnm3].
                             ---- rewrite Hnm3 in Hn. simpl in Hn. lia.
                             ---- destruct (Z.eq_dec n (-4)) as [Hnm4|Hnm4].
                                  ++++ rewrite Hnm4 in Hn. simpl in Hn. lia.
                                  ++++ destruct (Z.eq_dec n (-5)) as [Hnm5|Hnm5].
                                       **** rewrite Hnm5 in Hn. simpl in Hn. lia.
                                       **** assert (n >= 6 \/ n <= -6) as Hbig by lia.
                                            destruct Hbig as [Hbig|Hbig].
                                            { assert (n * n * n >= 216) by nia. lia. }
                                            { assert (n * n * n <= -216) by nia. lia. }
Qed.