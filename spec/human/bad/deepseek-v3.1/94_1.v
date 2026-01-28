Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum_digits_fueled (n fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match n with
    | 0 => 0
    | _ => (n mod 10) + sum_digits_fueled (n / 10) fuel'
    end
  end.

Definition sum_digits (n : nat) : nat :=
  sum_digits_fueled n n.

Definition problem_94_pre (lst : list nat) : Prop := True.

Definition problem_94_spec (lst : list nat) (output : nat) : Prop :=
  (exists p,
    In p lst /\
    prime (Z.of_nat p) /\
    (forall p', In p' lst -> prime (Z.of_nat p') -> (p' <= p)%nat) /\
    output = sum_digits p)
  \/
  ((forall x, In x lst -> ~ prime (Z.of_nat x)) /\ output = 0).

Lemma prime_181 : prime (Z.of_nat 181).
Proof.
  apply prime_intro.
  - unfold Z.lt. simpl. lia.
  - intros n [Hdiv H1].
    assert (1 < Z.abs n < 181 \/ Z.abs n = 181) by lia.
    destruct H as [H|H].
    + assert (H2: Z.abs n ≤ 13) by lia.
      destruct (Z_le_lt_eq_dec (Z.abs n) 13 H2); try lia.
      intro H3; apply Z.divide_1_r in H3; lia.
    + subst n; auto.
Qed.

Lemma prime_7 : prime (Z.of_nat 7).
Proof.
  apply prime_intro.
  - unfold Z.lt. simpl. lia.
  - intros n [Hdiv H1].
    assert (1 < Z.abs n < 7 \/ Z.abs n = 7) by lia.
    destruct H as [H|H].
    + lia.
    + subst n; auto.
Qed.

Lemma prime_5 : prime (Z.of_nat 5).
Proof.
  apply prime_intro.
  - unfold Z.lt. simpl. lia.
  - intros n [Hdiv H1].
    assert (1 < Z.abs n < 5 \/ Z.abs n = 5) by lia.
    destruct H as [H|H].
    + lia.
    + subst n; auto.
Qed.

Lemma prime_3 : prime (Z.of_nat 3).
Proof.
  apply prime_intro.
  - unfold Z.lt. simpl. lia.
  - intros n [Hdiv H1].
    assert (1 < Z.abs n < 3 \/ Z.abs n = 3) by lia.
    destruct H as [H|H].
    + lia.
    + subst n; auto.
Qed.

Lemma prime_2 : prime (Z.of_nat 2).
Proof.
  apply prime_intro.
  - unfold Z.lt. simpl. lia.
  - intros n [Hdiv H1].
    assert (1 < Z.abs n < 2 \/ Z.abs n = 2) by lia.
    destruct H as [H|H].
    + lia.
    + subst n; auto.
Qed.

Lemma not_prime_0 : ~ prime (Z.of_nat 0).
Proof.
  intro H. inversion H. lia.
Qed.

Lemma not_prime_1 : ~ prime (Z.of_nat 1).
Proof.
  intro H. inversion H. lia.
Qed.

Lemma not_prime_4 : ~ prime (Z.of_nat 4).
Proof.
  intro H.
  assert (2 | 4) by (exists 2; lia).
  inversion H. apply H2 in H0; lia.
Qed.

Lemma not_prime_32 : ~ prime (Z.of_nat 32).
Proof.
  intro H.
  assert (2 | 32) by (exists 16; lia).
  inversion H. apply H2 in H0; lia.
Qed.

Lemma not_prime_324 : ~ prime (Z.of_nat 324).
Proof.
  intro H.
  assert (2 | 324) by (exists 162; lia).
  inversion H. apply H2 in H0; lia.
Qed.

Lemma sum_digits_181 : sum_digits 181 = 10.
Proof.
  unfold sum_digits, sum_digits_fueled.
  simpl. reflexivity.
Qed.

Example test_case_1 : problem_94_spec [0;3;2;1;3;5;7;4;5;5;5;2;181;32;4;32;3;2;32;324;4;3] 10.
Proof.
  left. exists 181.
  repeat split.
  - unfold In. do 12 right. left. reflexivity.
  - apply prime_181.
  - intros p' H Hprime.
    destruct H as [H|H]; [subst p'|].
    + exfalso. apply not_prime_0. assumption.
    + destruct H as [H|H]; [subst p'|].
      * lia.
      + destruct H as [H|H]; [subst p'|].
        * lia.
        + destruct H as [H|H]; [subst p'|].
          * exfalso. apply not_prime_1. assumption.
          + destruct H as [H|H]; [subst p'|].
            * lia.
            + destruct H as [H|H]; [subst p'|].
              * lia.
              + destruct H as [H|H]; [subst p'|].
                * lia.
                + destruct H as [H|H]; [subst p'|].
                  * exfalso. apply not_prime_4. assumption.
                  + destruct H as [H|H]; [subst p'|].
                    * lia.
                    + destruct H as [H|H]; [subst p'|].
                      * lia.
                      + destruct H as [H|H]; [subst p'|].
                        * lia.
                        + destruct H as [H|H]; [subst p'|].
                          * lia.
                          + destruct H as [H|H]; [subst p'|].
                            * lia.
                            + destruct H as [H|H]; [subst p'|].
                              * exfalso. apply not_prime_32. assumption.
                              + destruct H as [H|H]; [subst p'|].
                                * exfalso. apply not_prime_4. assumption.
                                + destruct H as [H|H]; [subst p'|].
                                  * exfalso. apply not_prime_32. assumption.
                                  + destruct H as [H|H]; [subst p'|].
                                    * lia.
                                    + destruct H as [H|H]; [subst p'|].
                                      * lia.
                                      + destruct H as [H|H]; [subst p'|].
                                        * exfalso. apply not_prime_32. assumption.
                                        + destruct H as [H|H]; [subst p'|].
                                          * exfalso. apply not_prime_324. assumption.
                                          + destruct H as [H|H]; [subst p'|].
                                            * exfalso. apply not_prime_4. assumption.
                                            + destruct H as [H|H]; [subst p'|].
                                              * lia.
                                              + contradiction.
  - apply sum_digits_181.
Qed.