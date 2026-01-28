Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* Pre: n must be > 1 and not prime for this spec to be meaningful *)
Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

Definition problem_59_spec (n p: Z) : Prop :=
  (
    prime p /\ (p | n) /\
    (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)
  ).

Lemma pos_factors_of_5 : forall a b, 0 < a -> 0 < b -> a * b = 5 -> a = 1 \/ a = 5.
Proof.
  intros a b Ha Hb H.
  assert (Ha_ge1 : 1 <= a) by lia.
  destruct (Z_le_gt_dec a 2) as [Ha_le2 | Ha_ge3].
  - (* 1 <= a <= 2 *)
    destruct (Z.eq_dec a 1) as [->|Ha1].
    + left; lia.
    + assert (a = 2) by lia. subst a. lia.
  - (* a >= 3 *)
    destruct (Z_le_gt_dec b 1) as [Hb_le1 | Hb_gt1].
    + assert (b = 1) by lia. subst b. right. lia.
    + assert (2 <= b) by lia.
      assert (Hlb: 3 * 2 <= a * b).
      { apply Z.le_trans with (m := 3 * b).
        - apply Z.mul_le_mono_nonneg_l; lia.
        - apply Z.mul_le_mono_nonneg_r; lia.
      }
      rewrite H in Hlb. lia.
Qed.

Lemma prime_5 : prime 5%Z.
Proof.
  unfold prime.
  split; [lia|].
  intros a b H.
  assert (Ha0 : a <> 0).
  { intro Ha; subst; simpl in H; lia. }
  assert (Hb0 : b <> 0).
  { intro Hb; subst; simpl in H; lia. }
  destruct (Z_lt_ge_dec a 0) as [Ha_neg | Ha_ge0].
  - (* a < 0 -> b < 0 *)
    assert (Hb_neg : b < 0).
    { (* if b >= 0 then a*b <= 0, contradicting 5 *)
      destruct (Z_le_gt_dec b 0) as [Hb_le0|Hb_gt0]; [lia|].
      exfalso. (* Hb_gt0 cannot happen since a<0 and b>0 => product < 0 *)
      assert (a * b < 0) by (apply Z.mul_pos_neg; lia).
      lia.
    }
    set (a' := -a).
    set (b' := -b).
    assert (Ha'pos : 0 < a') by (subst a'; lia).
    assert (Hb'pos : 0 < b') by (subst b'; lia).
    replace a with (- a') in H by (subst a'; lia).
    replace b with (- b') in H by (subst b'; lia).
    rewrite Z.mul_opp_opp in H.
    apply pos_factors_of_5 in H; try assumption.
    destruct H as [Ha'1|Ha'5]; subst a';
    [right; right; left; lia | right; right; right; lia].
  - (* a >= 0 *)
    assert (Ha_pos : 0 < a) by (destruct (Z.eq_dec a 0); [contradiction|lia]).
    (* b must be positive *)
    assert (Hb_pos : 0 < b).
    { destruct (Z_le_gt_dec b 0) as [Hb_le0|Hb_gt0]; [exfalso; subst; simpl in H; lia|assumption]. }
    apply pos_factors_of_5 in H; try assumption.
    destruct H as [Ha1|Ha5]; subst; [left; lia | right; left; lia].
Qed.

Example problem_59_example_15_5 : problem_59_spec 15%Z 5%Z.
Proof.
  unfold problem_59_spec.
  split.
  - apply prime_5.
  - split.
    + exists 3%Z. reflexivity.
    + intros q [Hqprime Hqdiv].
      replace 15%Z with (3%Z * 5%Z) in Hqdiv by reflexivity.
      pose proof (prime_mult Hqprime 3%Z 5%Z Hqdiv) as [Hq3 | Hq5].
      * destruct Hq3 as [k Hk].
        (* q | 3 -> 3 = q * k; since q > 1 and 3 > 0, k >= 1; thus q <= 3 <= 5 *)
        destruct Hqprime as [Hqgt1 _].
        assert (0 <= q) by lia.
        assert (1 <= Z.abs k).
        { destruct (Z.eq_dec (Z.abs k) 0) as [Hz|Hz]; [rewrite Hz in Hk; simpl in Hk; lia|lia]. }
        assert (Habs: 3 = q * Z.abs k).
        { rewrite <- Z.abs_mul, Hk. now rewrite Z.abs_eq by lia. }
        assert (q * 1 <= q * Z.abs k) by (apply Z.mul_le_mono_nonneg_l; lia).
        rewrite Habs in H. lia.
      * destruct Hq5 as [k Hk].
        destruct Hqprime as [Hqgt1 _].
        assert (0 <= q) by lia.
        assert (1 <= Z.abs k).
        { destruct (Z.eq_dec (Z.abs k) 0) as [Hz|Hz]; [rewrite Hz in Hk; simpl in Hk; lia|lia]. }
        assert (Habs: 5 = q * Z.abs k).
        { rewrite <- Z.abs_mul, Hk. now rewrite Z.abs_eq by lia. }
        assert (q * 1 <= q * Z.abs k) by (apply Z.mul_le_mono_nonneg_l; lia).
        rewrite Habs in H. lia.
Qed.