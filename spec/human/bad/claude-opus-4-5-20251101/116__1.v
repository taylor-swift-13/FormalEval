Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.
Require Import Sorting.Sorted.
Require Import Lia.
Import ListNotations.

Inductive count_ones_helper_rel : nat -> nat -> nat -> Prop :=
| cohr_zero_fuel : forall n, count_ones_helper_rel n 0 0
| cohr_zero_n : forall fuel, count_ones_helper_rel 0 fuel 0
| cohr_step : forall n fuel fuel' ones_tail,
    fuel = S fuel' ->
    n <> 0 ->
    count_ones_helper_rel (n / 2) fuel' ones_tail ->
    count_ones_helper_rel n fuel ((n mod 2) + ones_tail).

Inductive count_ones_rel : nat -> nat -> Prop :=
| cor_base : forall n ones, count_ones_helper_rel n n ones -> count_ones_rel n ones.

Definition lt_custom (a b : nat) : Prop :=
  exists ones_a ones_b,
    count_ones_rel a ones_a /\
    count_ones_rel b ones_b /\
    ((ones_a < ones_b) \/ (ones_a = ones_b /\ a < b)).

Definition lt_custom_bool (a b : nat) : Prop :=
  exists ones_a ones_b,
    count_ones_rel a ones_a /\
    count_ones_rel b ones_b /\
    ((ones_a <? ones_b) = true \/ ((ones_a =? ones_b) = true /\ (a <? b) = true)).

Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
  | isr_nil : forall x, insert_sorted_rel x [] [x]
  | isr_insert : forall x h t,
      lt_custom_bool x h ->
      insert_sorted_rel x (h :: t) (x :: h :: t)
  | isr_skip : forall x h t result,
      ~ lt_custom_bool x h ->
      insert_sorted_rel x t result ->
      insert_sorted_rel x (h :: t) (h :: result).

Inductive sort_array_impl_rel : list nat -> list nat -> Prop :=
| sair_nil : sort_array_impl_rel [] []
| sair_cons : forall h t sorted_tail result,
    sort_array_impl_rel t sorted_tail ->
    insert_sorted_rel h sorted_tail result ->
    sort_array_impl_rel (h :: t) result.

Definition problem_116_pre (input : list nat) : Prop := True.

Definition problem_116_spec (input output : list nat) : Prop :=
  sort_array_impl_rel input output.

(* Helper lemmas for count_ones *)
Lemma count_ones_0 : count_ones_rel 0 0.
Proof.
  apply cor_base.
  apply cohr_zero_n.
Qed.

Lemma count_ones_1 : count_ones_rel 1 1.
Proof.
  apply cor_base.
  apply (cohr_step 1 1 0 0).
  - reflexivity.
  - lia.
  - simpl. apply cohr_zero_n.
Qed.

Lemma count_ones_2 : count_ones_rel 2 1.
Proof.
  apply cor_base.
  apply (cohr_step 2 2 1 1).
  - reflexivity.
  - lia.
  - simpl. apply (cohr_step 1 1 0 0).
    + reflexivity.
    + lia.
    + simpl. apply cohr_zero_n.
Qed.

Lemma count_ones_3 : count_ones_rel 3 2.
Proof.
  apply cor_base.
  apply (cohr_step 3 3 2 1).
  - reflexivity.
  - lia.
  - simpl. apply (cohr_step 1 2 1 0).
    + reflexivity.
    + lia.
    + simpl. apply cohr_zero_n.
Qed.

Lemma count_ones_4 : count_ones_rel 4 1.
Proof.
  apply cor_base.
  apply (cohr_step 4 4 3 1).
  - reflexivity.
  - lia.
  - simpl. apply (cohr_step 2 3 2 1).
    + reflexivity.
    + lia.
    + simpl. apply (cohr_step 1 2 1 0).
      * reflexivity.
      * lia.
      * simpl. apply cohr_zero_n.
Qed.

Lemma count_ones_5 : count_ones_rel 5 2.
Proof.
  apply cor_base.
  apply (cohr_step 5 5 4 1).
  - reflexivity.
  - lia.
  - simpl. apply (cohr_step 2 4 3 1).
    + reflexivity.
    + lia.
    + simpl. apply (cohr_step 1 3 2 0).
      * reflexivity.
      * lia.
      * simpl. apply cohr_zero_n.
Qed.

(* lt_custom_bool proofs *)
Lemma lt_1_2 : lt_custom_bool 1 2.
Proof.
  exists 1, 1.
  split. exact count_ones_1.
  split. exact count_ones_2.
  right. split; reflexivity.
Qed.

Lemma lt_1_4 : lt_custom_bool 1 4.
Proof.
  exists 1, 1.
  split. exact count_ones_1.
  split. exact count_ones_4.
  right. split; reflexivity.
Qed.

Lemma lt_2_4 : lt_custom_bool 2 4.
Proof.
  exists 1, 1.
  split. exact count_ones_2.
  split. exact count_ones_4.
  right. split; reflexivity.
Qed.

Lemma lt_4_3 : lt_custom_bool 4 3.
Proof.
  exists 1, 2.
  split. exact count_ones_4.
  split. exact count_ones_3.
  left. reflexivity.
Qed.

Lemma lt_4_5 : lt_custom_bool 4 5.
Proof.
  exists 1, 2.
  split. exact count_ones_4.
  split. exact count_ones_5.
  left. reflexivity.
Qed.

Lemma lt_3_5 : lt_custom_bool 3 5.
Proof.
  exists 2, 2.
  split. exact count_ones_3.
  split. exact count_ones_5.
  right. split; reflexivity.
Qed.

(* Uniqueness of count_ones_helper *)
Lemma count_ones_helper_unique : forall n fuel ones1 ones2,
  count_ones_helper_rel n fuel ones1 ->
  count_ones_helper_rel n fuel ones2 ->
  ones1 = ones2.
Proof.
  intros n fuel. revert n.
  induction fuel; intros n ones1 ones2 H1 H2.
  - inversion H1; subst.
    + inversion H2; subst. reflexivity.
    + inversion H2; subst. reflexivity.
    + discriminate.
  - inversion H1; subst.
    + inversion H2; subst.
      * reflexivity.
      * reflexivity.
      * discriminate.
    + inversion H2; subst.
      * reflexivity.
      * reflexivity.
      * contradiction.
    + inversion H2; subst.
      * discriminate.
      * contradiction.
      * injection H as Hfuel. subst fuel'0.
        assert (ones_tail = ones_tail0).
        { apply (IHfuel (n / 2)); assumption. }
        lia.
Qed.

Lemma count_ones_unique : forall n ones1 ones2,
  count_ones_rel n ones1 ->
  count_ones_rel n ones2 ->
  ones1 = ones2.
Proof.
  intros n ones1 ones2 H1 H2.
  inversion H1; subst.
  inversion H2; subst.
  eapply count_ones_helper_unique; eassumption.
Qed.

(* Not lt_custom_bool proofs *)
Lemma not_lt_4_1 : ~ lt_custom_bool 4 1.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 1) by (eapply count_ones_unique; [exact Ha | exact count_ones_4]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_1]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_4_2 : ~ lt_custom_bool 4 2.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 1) by (eapply count_ones_unique; [exact Ha | exact count_ones_4]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_2]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_3_1 : ~ lt_custom_bool 3 1.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_3]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_1]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_3_2 : ~ lt_custom_bool 3 2.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_3]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_2]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_3_4 : ~ lt_custom_bool 3 4.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_3]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_4]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_5_1 : ~ lt_custom_bool 5 1.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_5]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_1]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_5_2 : ~ lt_custom_bool 5 2.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_5]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_2]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_5_4 : ~ lt_custom_bool 5 4.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_5]).
  assert (ones_b = 1) by (eapply count_ones_unique; [exact Hb | exact count_ones_4]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Lemma not_lt_5_3 : ~ lt_custom_bool 5 3.
Proof.
  intros [ones_a [ones_b [Ha [Hb H]]]].
  assert (ones_a = 2) by (eapply count_ones_unique; [exact Ha | exact count_ones_5]).
  assert (ones_b = 2) by (eapply count_ones_unique; [exact Hb | exact count_ones_3]).
  subst.
  destruct H as [H | [H1 H2]].
  - discriminate.
  - discriminate.
Qed.

Example problem_116_test : problem_116_spec [1; 5; 2; 3; 4] [1; 2; 4; 3; 5].
Proof.
  unfold problem_116_spec.
  apply (sair_cons 1 [5; 2; 3; 4] [2; 4; 3; 5] [1; 2; 4; 3; 5]).
  - apply (sair_cons 5 [2; 3; 4] [2; 4; 3] [2; 4; 3; 5]).
    + apply (sair_cons 2 [3; 4] [4; 3] [2; 4; 3]).
      * apply (sair_cons 3 [4] [4] [4; 3]).
        -- apply (sair_cons 4 [] [] [4]).
           ++ apply sair_nil.
           ++ apply isr_nil.
        -- apply isr_skip.
           ++ exact not_lt_3_4.
           ++ apply isr_nil.
      * apply isr_insert.
        exact lt_2_4.
    + apply isr_skip.
      * exact not_lt_5_2.
      * apply isr_skip.
        -- exact not_lt_5_4.
        -- apply isr_skip.
           ++ exact not_lt_5_3.
           ++ apply isr_nil.
  - apply isr_insert.
    exact lt_1_2.
Qed.