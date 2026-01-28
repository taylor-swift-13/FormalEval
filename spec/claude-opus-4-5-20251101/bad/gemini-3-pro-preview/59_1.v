Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* Specification Definitions *)
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

(* Proof for Test Case: input = 15, output = 5 *)
Example test_largest_prime_factor_15 : largest_prime_factor_spec 15 5.
Proof.
  unfold largest_prime_factor_spec.
  split.
  - (* Goal 1: 15 > 1 *)
    lia.
  - split.
    + (* Goal 2: ~ is_prime 15 *)
      intro H.
      unfold is_prime in H.
      destruct H as [_ Hforall].
      specialize (Hforall 3).
      assert (1 < 3 < 15) by lia.
      apply Hforall in H.
      (* 15 % 3 = 0, contradiction *)
      compute in H.
      congruence.
    + split.
      * (* Goal 3: is_prime_factor 5 15 *)
        unfold is_prime_factor.
        split.
        -- (* is_prime 5 *)
           unfold is_prime.
           split.
           ++ lia.
           ++ intros d Hd.
              assert (d = 2 \/ d = 3 \/ d = 4) by lia.
              destruct H as [-> | [-> | ->]]; compute; discriminate.
        -- (* is_factor 5 15 *)
           unfold is_factor.
           reflexivity.
      * (* Goal 4: forall f, is_prime_factor f 15 -> f <= 5 *)
        intros f [Hprime Hfactor].
        unfold is_factor in Hfactor.
        destruct Hprime as [Hgt1 Hprime_forall].
        
        (* First, prove f <= 15 *)
        assert (f <= 15).
        {
          destruct (Z_le_gt_dec f 15).
          - assumption.
          - (* If f > 15, rem 15 f = 15 <> 0 *)
            assert (Z.rem 15 f = 15).
            { apply Z.rem_small. lia. }
            rewrite H in Hfactor.
            discriminate.
        }
        
        (* Now perform case analysis on f in range [2, 15] *)
        assert (f = 2 \/ f = 3 \/ f = 4 \/ f = 5 \/ f = 6 \/ f = 7 \/ f = 8 \/ 
                f = 9 \/ f = 10 \/ f = 11 \/ f = 12 \/ f = 13 \/ f = 14 \/ f = 15) by lia.
        
        destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]].
        -- (* f = 2 *) compute in Hfactor; discriminate.
        -- (* f = 3 *) lia. (* 3 <= 5 holds *)
        -- (* f = 4 *) compute in Hfactor; discriminate.
        -- (* f = 5 *) lia. (* 5 <= 5 holds *)
        -- (* f = 6 *) compute in Hfactor; discriminate.
        -- (* f = 7 *) compute in Hfactor; discriminate.
        -- (* f = 8 *) compute in Hfactor; discriminate.
        -- (* f = 9 *) compute in Hfactor; discriminate.
        -- (* f = 10 *) compute in Hfactor; discriminate.
        -- (* f = 11 *) compute in Hfactor; discriminate.
        -- (* f = 12 *) compute in Hfactor; discriminate.
        -- (* f = 13 *) compute in Hfactor; discriminate.
        -- (* f = 14 *) compute in Hfactor; discriminate.
        -- (* f = 15 *) 
           (* 15 is a factor but not prime *)
           specialize (Hprime_forall 3).
           assert (1 < 3 < 15) by lia.
           apply Hprime_forall in H.
           compute in H.
           congruence.
Qed.