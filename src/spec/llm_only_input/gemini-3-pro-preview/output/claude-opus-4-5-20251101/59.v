Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p > 1 /\ forall d : Z, 1 < d < p -> Z.rem p d <> 0.

Definition is_factor (f n : Z) : Prop :=
  Z.rem n f = 0.

Definition is_prime_factor (f n : Z) : Prop :=
  is_prime f /\ is_factor f n.

Definition largest_prime_factor_spec (n : Z) (result : Z) : Prop :=
  n > 1 /\
  ~(is_prime n) /\
  is_prime_factor result n /\
  (forall f : Z, is_prime_factor f n -> f <= result).

Example test_15_5 : largest_prime_factor_spec 15 5.
Proof.
  unfold largest_prime_factor_spec.
  split; [| split; [| split]].
  - (* Prove 15 > 1 *)
    lia.
  - (* Prove ~ is_prime 15 *)
    intros H. destruct H as [_ H].
    specialize (H 3).
    assert (1 < 3 < 15) by lia.
    apply H in H0.
    compute in H0. congruence.
  - (* Prove is_prime_factor 5 15 *)
    split.
    + (* is_prime 5 *)
      split; [lia |].
      intros d Hd.
      assert (d = 2 \/ d = 3 \/ d = 4) by lia.
      destruct H as [? | [? | ?]]; subst; compute; discriminate.
    + (* is_factor 5 15 *)
      reflexivity.
  - (* Prove forall f, is_prime_factor f 15 -> f <= 5 *)
    intros f [Hf_prime Hf_factor].
    unfold is_factor in Hf_factor.
    destruct (Z_le_gt_dec f 5).
    + (* f <= 5 *)
      assumption.
    + (* f > 5 *)
      destruct (Z_le_gt_dec f 15).
      * (* 5 < f <= 15 *)
        assert (f = 6 \/ f = 7 \/ f = 8 \/ f = 9 \/ f = 10 \/ 
                f = 11 \/ f = 12 \/ f = 13 \/ f = 14 \/ f = 15) by lia.
        destruct H as [?|[?|[?|[?|[?|[?|[?|[?|[?|?]]]]]]]]]; subst;
          try (compute in Hf_factor; discriminate).
        (* Case f = 15: is a factor, but not prime *)
        destruct Hf_prime as [_ Hprime].
        specialize (Hprime 3).
        assert (1 < 3 < 15) by lia.
        apply Hprime in H. compute in H. congruence.
      * (* f > 15 *)
        assert (Hrem: Z.rem 15 f = 15).
        { apply Z.rem_small. lia. }
        rewrite Hrem in Hf_factor.
        discriminate.
Qed.