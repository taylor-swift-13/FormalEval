Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Require Import Sorting.Sorted.
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

Lemma count_ones_1 : count_ones_rel 1 1.
Proof.
  apply cor_base. apply cohr_step with (fuel' := 0) (ones_tail := 0); auto.
  - discriminate.
  - apply cohr_zero_n.
Qed.

Lemma count_ones_2 : count_ones_rel 2 1.
Proof.
  apply cor_base. apply cohr_step with (fuel' := 1) (ones_tail := 0); auto.
  - discriminate.
  - apply cohr_step with (fuel' := 0) (ones_tail := 0); auto.
    + discriminate.
    + apply cohr_zero_n.
Qed.

Lemma count_ones_3 : count_ones_rel 3 2.
Proof.
  apply cor_base. apply cohr_step with (fuel' := 1) (ones_tail := 1); auto.
  - discriminate.
  - apply cohr_step with (fuel' := 0) (ones_tail := 0); auto.
    + discriminate.
    + apply cohr_zero_n.
Qed.

Lemma count_ones_4 : count_ones_rel 4 1.
Proof.
  apply cor_base. apply cohr_step with (fuel' := 2) (ones_tail := 0); auto.
  - discriminate.
  - apply cohr_step with (fuel' := 1) (ones_tail := 0); auto.
    + discriminate.
    + apply cohr_step with (fuel' := 0) (ones_tail := 0); auto.
      * discriminate.
      * apply cohr_zero_n.
Qed.

Lemma count_ones_5 : count_ones_rel 5 2.
Proof.
  apply cor_base. apply cohr_step with (fuel' := 2) (ones_tail := 1); auto.
  - discriminate.
  - apply cohr_step with (fuel' := 1) (ones_tail := 0); auto.
    + discriminate.
    + apply cohr_step with (fuel' := 0) (ones_tail := 0); auto.
      * discriminate.
      * apply cohr_zero_n.
Qed.

Example problem_116_test_case : problem_116_spec [1; 5; 2; 3; 4] [1; 2; 3; 4; 5].
Proof.
  unfold problem_116_spec.
  eapply sair_cons.
  - eapply sair_cons.
    + eapply sair_cons.
      * eapply sair_cons.
        -- eapply sair_cons.
           ++ apply sair_nil.
           ++ eapply isr_nil.
        -- eapply isr_insert.
           ++ unfold lt_custom_bool.
              exists 2, 1.
              split; [apply count_ones_3 |].
              split; [apply count_ones_4 |].
              left. simpl. reflexivity.
      * eapply isr_insert.
        -- unfold lt_custom_bool.
           exists 1, 1.
           split; [apply count_ones_2 |].
           split; [apply count_ones_1 |].
           right. split; simpl; reflexivity.
    + eapply isr_insert.
      * unfold lt_custom_bool.
        exists 1, 2.
        split; [apply count_ones_1 |].
        split; [apply count_ones_5 |].
        left. simpl. reflexivity.
  - eapply isr_insert.
    + unfold lt_custom_bool.
      exists 1, 1.
      split; [apply count_ones_1 |].
      split; [apply count_ones_1 |].
      right. split; simpl; reflexivity.
Qed.