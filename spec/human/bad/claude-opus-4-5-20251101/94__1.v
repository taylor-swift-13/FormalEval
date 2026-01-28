Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Require Import Lia.
Import ListNotations.
Open Scope nat_scope.

Inductive sum_digits_fueled_rel : nat -> nat -> nat -> Prop :=
  | sdfr_zero_fuel : forall n, sum_digits_fueled_rel n 0 0
  | sdfr_zero_n : forall fuel, sum_digits_fueled_rel 0 fuel 0
  | sdfr_step : forall n fuel fuel' sum_tail,
      fuel = S fuel' ->
      n <> 0 ->
      sum_digits_fueled_rel (n / 10) fuel' sum_tail ->
      sum_digits_fueled_rel n fuel ((n mod 10) + sum_tail).

Inductive sum_digits_rel : nat -> nat -> Prop :=
  | sdr_base : forall n sum, sum_digits_fueled_rel n n sum -> sum_digits_rel n sum.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> p' <= p) /\
    sum_digits_rel p output)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Lemma prime_181 : prime 181.
Proof.
  apply prime_intro.
  - lia.
  - intros n Hn Hdiv.
    destruct (Z.eq_dec n 1) as [|Hn1]; [left; auto|].
    destruct (Z.eq_dec n 181) as [|Hn181]; [right; auto|].
    exfalso.
    assert (Hbound: 2 <= n <= 180) by lia.
    destruct Hdiv as [k Hk].
    assert (Hk_pos: k > 0).
    { destruct (Z.le_gt_cases k 0); try lia.
      assert (n * k <= 0) by (apply Z.mul_nonneg_nonpos; lia).
      lia. }
    assert (Hk_bound: k < 181).
    { destruct (Z.le_gt_cases 181 k); try lia.
      assert (n * k >= 2 * 181) by nia. lia. }
    assert (Hn_bound: n <= 13).
    { destruct (Z.le_gt_cases n 13); auto.
      assert (k <= 13).
      { destruct (Z.le_gt_cases k 13); auto.
        assert (n * k > 181) by nia. lia. }
      assert (n * k <= 13 * 13) by nia.
      assert (13 * 13 = 169) by lia.
      lia. }
    assert (n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13) by lia.
    destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]]]];
    nia.
Qed.

Lemma sum_digits_181_eq_10 : sum_digits_rel 181 10.
Proof.
  apply sdr_base.
  eapply sdfr_step with (fuel' := 180).
  - reflexivity.
  - lia.
  - simpl.
    eapply sdfr_step with (fuel' := 17).
    + reflexivity.
    + lia.
    + simpl.
      eapply sdfr_step with (fuel' := 0).
      * reflexivity.
      * lia.
      * simpl. apply sdfr_zero_fuel.
Qed.

Lemma not_prime_0 : ~ prime 0.
Proof.
  intro H. destruct H. lia.
Qed.

Lemma not_prime_1 : ~ prime 1.
Proof.
  intro H. destruct H. lia.
Qed.

Lemma not_prime_4 : ~ prime 4.
Proof.
  intro H. destruct H.
  specialize (H0 2 ltac:(lia)).
  assert (2 | 4)%Z by (exists 2; lia).
  specialize (H0 H1).
  lia.
Qed.

Lemma not_prime_32 : ~ prime 32.
Proof.
  intro H. destruct H.
  specialize (H0 2 ltac:(lia)).
  assert (2 | 32)%Z by (exists 16; lia).
  specialize (H0 H1).
  lia.
Qed.

Lemma not_prime_324 : ~ prime 324.
Proof.
  intro H. destruct H.
  specialize (H0 2 ltac:(lia)).
  assert (2 | 324)%Z by (exists 162; lia).
  specialize (H0 H1).
  lia.
Qed.

Example problem_94_test1 :
  problem_94_spec [0; 3; 2; 1; 3; 5; 7; 4; 5; 5; 5; 2; 181; 32; 4; 32; 3; 2; 32; 324; 4; 3] 10.
Proof.
  unfold problem_94_spec.
  left.
  exists 181.
  split; [|split; [|split]].
  - simpl. tauto.
  - exact prime_181.
  - intros p' Hp' Hprime'.
    simpl in Hp'.
    destruct Hp' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|->]]]]]]]]]]]]]]]]]]]]].
    + exfalso. apply not_prime_0. simpl in Hprime'. exact Hprime'.
    + lia.
    + lia.
    + exfalso. apply not_prime_1. simpl in Hprime'. exact Hprime'.
    + lia.
    + lia.
    + lia.
    + exfalso. apply not_prime_4. simpl in Hprime'. exact Hprime'.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + exfalso. apply not_prime_32. simpl in Hprime'. exact Hprime'.
    + exfalso. apply not_prime_4. simpl in Hprime'. exact Hprime'.
    + exfalso. apply not_prime_32. simpl in Hprime'. exact Hprime'.
    + lia.
    + lia.
    + exfalso. apply not_prime_32. simpl in Hprime'. exact Hprime'.
    + exfalso. apply not_prime_324. simpl in Hprime'. exact Hprime'.
    + exfalso. apply not_prime_4. simpl in Hprime'. exact Hprime'.
    + lia.
  - exact sum_digits_181_eq_10.
Qed.