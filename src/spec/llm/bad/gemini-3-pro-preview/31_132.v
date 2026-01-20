Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  result = true <-> prime n.

Fixpoint check_loop (d : Z) (fuel : nat) (n : Z) : bool :=
  match fuel with
  | O => false 
  | S f =>
      if (d * d >? n) then true
      else if (Z.rem n d =? 0) then false
      else check_loop (d + 1) f n
  end.

Definition check_prime (n : Z) : bool :=
  if (n <? 2) then false
  else check_loop 2 (Z.to_nat (Z.sqrt n) + 2) n.

Lemma check_loop_correct : forall fuel d n,
  2 <= d ->
  check_loop d fuel n = true ->
  (forall k, d <= k -> k * k <= n -> ~ (k | n)).
Proof.
  induction fuel; intros d n Hd Hres k Hk1 Hk2 Hdiv.
  - simpl in Hres. discriminate.
  - simpl in Hres.
    destruct (d * d >? n) eqn:Hstop.
    + apply Z.gtb_gt in Hstop.
      assert (d * d <= k * k).
      { apply Z.mul_le_mono_nonneg; lia. }
      lia.
    + apply Z.gtb_le in Hstop.
      destruct (Z.rem n d =? 0) eqn:Hrem.
      * discriminate.
      * apply Z.eqb_neq in Hrem.
        assert (Hnd: ~ (d | n)).
        { intros H. apply Z.rem_divide in H; try lia. congruence. }
        assert (k = d \/ d + 1 <= k) by lia.
        destruct H as [Heq | Hgt].
        -- subst. assumption.
        -- eapply IHfuel; try eassumption.
           lia.
Qed.

Lemma check_prime_correct : forall n, check_prime n = true -> prime n.
Proof.
  intros n H.
  unfold check_prime in H.
  destruct (n <? 2) eqn:Hlt.
  - discriminate.
  - apply Z.ltb_ge in Hlt.
    destruct (prime_dec n) as [Hp|Hnp]; auto.
    exfalso.
    apply not_prime_divide in Hnp; auto.
    destruct Hnp as [d [Hdiv_d Hrange]].
    assert (Hchecked: forall k, 2 <= k -> k * k <= n -> ~ (k | n)).
    { eapply check_loop_correct; eauto. lia. }
    assert (d * d <= n \/ n < d * d) by lia.
    destruct H0 as [Hsmall | Hlarge].
    + apply (Hchecked d); try lia; try assumption.
    + pose (d' := n / d).
      assert (Hdiv_d': (d' | n)).
      { exists d. rewrite Z.mul_comm. apply Z.div_exact; auto. lia. }
      assert (Heq: d * d' = n).
      { symmetry. apply Z.div_exact; auto. lia. }
      assert (Hd'_range: 1 < d').
      {
         assert (d * d' = n) by (rewrite Heq; reflexivity).
         destruct (Z.le_gt_cases d' 1).
         * assert (d * d' <= d * 1) by (apply Z.mul_le_mono_nonneg_l; lia).
           rewrite Heq in H0. lia.
         * assumption.
      }
      assert (d' * d' <= n).
      {
         assert (d' * d' < d * d')%Z.
         { apply Z.mul_lt_mono_pos_r; try lia.
           rewrite <- Heq.
           assert (d * d > d * d'). rewrite Heq. assumption.
           apply Z.mul_lt_mono_pos_l in H0; lia.
         }
         rewrite Heq in H0. lia.
      }
      apply (Hchecked d'); try lia; try assumption.
Qed.

Example test_is_prime_9999991 : is_prime_spec 9999991 true.
Proof.
  unfold is_prime_spec.
  split; intros H.
  - apply check_prime_correct.
    vm_compute. reflexivity.
  - reflexivity.
Qed.