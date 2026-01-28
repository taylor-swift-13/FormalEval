Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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

(* Helper: ones must be 0 when n = 0 *)
Lemma count_ones_helper_rel_zero : forall fuel ones,
  count_ones_helper_rel 0 fuel ones -> ones = 0.
Proof.
  intros fuel ones H. inversion H; subst.
  - reflexivity.
  - reflexivity.
  - exfalso. apply H1. reflexivity.
Qed.

(* Helper constructions for specific numbers *)
Lemma cohr_1_1_1 : count_ones_helper_rel 1 1 1.
Proof.
  eapply cohr_step with (fuel' := 0) (ones_tail := 0).
  - reflexivity.
  - discriminate.
  - apply cohr_zero_fuel.
Qed.

Lemma cohr_2_2_1 : count_ones_helper_rel 2 2 1.
Proof.
  (* 2 -> (2 mod 2)=0 + count_ones(1) *)
  eapply cohr_step with (fuel' := 1) (ones_tail := 1).
  - reflexivity.
  - discriminate.
  - (* count_ones_helper_rel 1 1 1 *)
    exact cohr_1_1_1.
Qed.

Lemma cohr_3_3_2 : count_ones_helper_rel 3 3 2.
Proof.
  (* 3 -> (3 mod 2)=1 + count_ones(1)=1 *)
  eapply cohr_step with (fuel' := 2) (ones_tail := 1).
  - reflexivity.
  - discriminate.
  - (* count_ones_helper_rel 1 2 1 *)
    eapply cohr_step with (fuel' := 1) (ones_tail := 0).
    + reflexivity.
    + discriminate.
    + apply cohr_zero_n.
Qed.

Lemma cohr_4_4_1 : count_ones_helper_rel 4 4 1.
Proof.
  (* 4 -> (4 mod 2)=0 + count_ones(2)=1 *)
  eapply cohr_step with (fuel' := 3) (ones_tail := 1).
  - reflexivity.
  - discriminate.
  - (* count_ones_helper_rel 2 3 1 *)
    eapply cohr_step with (fuel' := 2) (ones_tail := 1).
    + reflexivity.
    + discriminate.
    + (* count_ones_helper_rel 1 2 1 *)
      eapply cohr_step with (fuel' := 1) (ones_tail := 0).
      * reflexivity.
      * discriminate.
      * apply cohr_zero_n.
Qed.

Lemma cohr_5_5_2 : count_ones_helper_rel 5 5 2.
Proof.
  (* 5 -> (5 mod 2)=1 + count_ones(2)=1 *)
  eapply cohr_step with (fuel' := 4) (ones_tail := 1).
  - reflexivity.
  - discriminate.
  - (* count_ones_helper_rel 2 4 1 *)
    eapply cohr_step with (fuel' := 3) (ones_tail := 1).
    + reflexivity.
    + discriminate.
    + (* count_ones_helper_rel 1 3 1 *)
      eapply cohr_step with (fuel' := 2) (ones_tail := 0).
      * reflexivity.
      * discriminate.
      * apply cohr_zero_n.
Qed.

(* Existence of count_ones_rel for specific numbers *)
Lemma cor_1_1 : count_ones_rel 1 1.
Proof. apply cor_base. exact cohr_1_1_1. Qed.

Lemma cor_2_1 : count_ones_rel 2 1.
Proof. apply cor_base. exact cohr_2_2_1. Qed.

Lemma cor_3_2 : count_ones_rel 3 2.
Proof. apply cor_base. exact cohr_3_3_2. Qed.

Lemma cor_4_1 : count_ones_rel 4 1.
Proof. apply cor_base. exact cohr_4_4_1. Qed.

Lemma cor_5_2 : count_ones_rel 5 2.
Proof. apply cor_base. exact cohr_5_5_2. Qed.

(* Uniqueness of ones for specific numbers under count_ones_rel *)
Lemma count_ones_rel_1_value : forall ones, count_ones_rel 1 ones -> ones = 1.
Proof.
  intros ones H. inversion H; subst.
  inversion H0; subst; try discriminate.
  (* cohr_step case *)
  inversion H1; subst. (* 1 = S fuel' -> fuel' = 0 *)
  simpl in H3. (* (1/2) = 0 *)
  specialize (count_ones_helper_rel_zero 0 ones_tail H3) as Hz.
  subst ones_tail.
  simpl. reflexivity.
Qed.

Lemma count_ones_rel_2_value : forall ones, count_ones_rel 2 ones -> ones = 1.
Proof.
  intros ones H. inversion H; subst.
  inversion H0; subst; try discriminate.
  (* step for n=2 *)
  inversion H1; subst. (* 2 = S fuel' -> fuel' = 1 *)
  simpl in H3. (* (2/2) = 1 *)
  (* now analyze tail: count_ones_helper_rel 1 1 ones_tail *)
  inversion H3; subst; try discriminate.
  (* step for n=1 *)
  inversion H2; subst. (* 1 = S fuel' -> fuel' = 0 *)
  simpl in H4. (* (1/2) = 0 *)
  specialize (count_ones_helper_rel_zero 0 ones_tail0 H4) as Hz.
  subst ones_tail0.
  simpl. reflexivity.
Qed.

Lemma count_ones_rel_3_value : forall ones, count_ones_rel 3 ones -> ones = 2.
Proof.
  intros ones H. inversion H; subst.
  inversion H0; subst; try discriminate.
  (* step for n=3 *)
  inversion H1; subst. (* 3 = S fuel' -> fuel' = 2 *)
  simpl in H3. (* (3/2) = 1 *)
  (* analyze tail: count_ones_helper_rel 1 2 ones_tail *)
  inversion H3; subst; try discriminate.
  (* step for n=1 *)
  inversion H2; subst. (* 2 = S fuel' -> fuel' = 1 *)
  simpl in H4. (* (1/2) = 0 *)
  specialize (count_ones_helper_rel_zero 0 ones_tail0 H4) as Hz.
  subst ones_tail0.
  simpl. reflexivity.
Qed.

Lemma count_ones_rel_4_value : forall ones, count_ones_rel 4 ones -> ones = 1.
Proof.
  intros ones H. inversion H; subst.
  inversion H0; subst; try discriminate.
  (* step for n=4 *)
  inversion H1; subst. (* 4 = S fuel' -> fuel' = 3 *)
  simpl in H3. (* (4/2) = 2 *)
  (* analyze tail: count_ones_helper_rel 2 3 ones_tail *)
  inversion H3; subst; try discriminate.
  (* step for n=2 *)
  inversion H2; subst. (* 3 = S fuel' -> fuel' = 2 *)
  simpl in H4. (* (2/2) = 1 *)
  (* analyze tail: count_ones_helper_rel 1 2 ones_tail0 *)
  inversion H4; subst; try discriminate.
  (* step for n=1 *)
  inversion H5; subst. (* 2 = S fuel' -> fuel' = 1 *)
  simpl in H7. (* (1/2) = 0 *)
  specialize (count_ones_helper_rel_zero 0 ones_tail1 H7) as Hz.
  subst ones_tail1.
  simpl. reflexivity.
Qed.

Lemma count_ones_rel_5_value : forall ones, count_ones_rel 5 ones -> ones = 2.
Proof.
  intros ones H. inversion H; subst.
  inversion H0; subst; try discriminate.
  (* step for n=5 *)
  inversion H1; subst. (* 5 = S fuel' -> fuel' = 4 *)
  simpl in H3. (* (5/2) = 2 *)
  (* analyze tail: count_ones_helper_rel 2 4 ones_tail *)
  inversion H3; subst; try discriminate.
  (* step for n=2 *)
  inversion H2; subst. (* 4 = S fuel' -> fuel' = 3 *)
  simpl in H4. (* (2/2) = 1 *)
  (* analyze tail: count_ones_helper_rel 1 3 ones_tail0 *)
  inversion H4; subst; try discriminate.
  (* step for n=1 *)
  inversion H5; subst. (* 3 = S fuel' -> fuel' = 2 *)
  simpl in H7. (* (1/2) = 0 *)
  specialize (count_ones_helper_rel_zero 0 ones_tail1 H7) as Hz.
  subst ones_tail1.
  simpl. reflexivity.
Qed.

(* lt_custom_bool lemmas *)
Lemma lt_custom_bool_1_2 : lt_custom_bool 1 2.
Proof.
  exists 1, 1. split; [apply cor_1_1|]. split; [apply cor_2_1|].
  right. split; simpl; reflexivity.
Qed.

Lemma lt_custom_bool_2_4 : lt_custom_bool 2 4.
Proof.
  exists 1, 1. split; [apply cor_2_1|]. split; [apply cor_4_1|].
  right. split; simpl; reflexivity.
Qed.

Lemma lt_custom_bool_false_3_4 : ~ lt_custom_bool 3 4.
Proof.
  intros H. destruct H as [oa [ob [Ha [Hb Hlt]]]].
  pose proof (count_ones_rel_3_value oa Ha) as Hoa.
  pose proof (count_ones_rel_4_value ob Hb) as Hob.
  subst oa ob.
  simpl in Hlt.
  destruct Hlt as [Hlt | [Heq Hltab]].
  - discriminate.
  - simpl in Heq. discriminate.
Qed.

Lemma lt_custom_bool_false_5_2 : ~ lt_custom_bool 5 2.
Proof.
  intros H. destruct H as [oa [ob [Ha [Hb Hlt]]]].
  pose proof (count_ones_rel_5_value oa Ha) as Hoa.
  pose proof (count_ones_rel_2_value ob Hb) as Hob.
  subst oa ob.
  simpl in Hlt.
  destruct Hlt as [Hlt | [Heq Hltab]].
  - discriminate.
  - simpl in Heq. discriminate.
Qed.

Lemma lt_custom_bool_false_5_4 : ~ lt_custom_bool 5 4.
Proof.
  intros H. destruct H as [oa [ob [Ha [Hb Hlt]]]].
  pose proof (count_ones_rel_5_value oa Ha) as Hoa.
  pose proof (count_ones_rel_4_value ob Hb) as Hob.
  subst oa ob.
  simpl in Hlt.
  destruct Hlt as [Hlt | [Heq Hltab]].
  - discriminate.
  - simpl in Heq. discriminate.
Qed.

Lemma lt_custom_bool_false_5_3 : ~ lt_custom_bool 5 3.
Proof.
  intros H. destruct H as [oa [ob [Ha [Hb Hlt]]]].
  pose proof (count_ones_rel_5_value oa Ha) as Hoa.
  pose proof (count_ones_rel_3_value ob Hb) as Hob.
  subst oa ob.
  simpl in Hlt.
  destruct Hlt as [Hlt | [Heq Hltab]].
  - discriminate.
  - simpl in Hltab. discriminate.
Qed.

Example problem_116_test_case :
  problem_116_spec [1; 5; 2; 3; 4] [1; 2; 4; 3; 5].
Proof.
  unfold problem_116_spec.
  (* Overall sort *)
  apply sair_cons with (sorted_tail := [2; 4; 3; 5]) (result := [1; 2; 4; 3; 5]).
  - (* Sort [5;2;3;4] -> [2;4;3;5] *)
    apply sair_cons with (sorted_tail := [2; 4; 3]) (result := [2; 4; 3; 5]).
    + (* Sort [2;3;4] -> [2;4;3] *)
      apply sair_cons with (sorted_tail := [4; 3]) (result := [2; 4; 3]).
      * (* Sort [3;4] -> [4;3] *)
        apply sair_cons with (sorted_tail := [4]) (result := [4; 3]).
        -- (* Sort [4] -> [4] *)
           apply sair_cons with (sorted_tail := []) (result := [4]).
           ++ apply sair_nil.
           ++ apply isr_nil.
        -- (* Insert 3 into [4] -> [4;3] *)
           apply isr_skip with (x := 3) (h := 4) (t := []) (result := [3]).
           ++ apply lt_custom_bool_false_3_4.
           ++ apply isr_nil.
      * (* Insert 2 into [4;3] -> [2;4;3] *)
        apply isr_insert with (x := 2) (h := 4) (t := [3]).
        -- apply lt_custom_bool_2_4.
    + (* Insert 5 into [2;4;3] -> [2;4;3;5] *)
      apply isr_skip with (x := 5) (h := 2) (t := [4; 3]) (result := [4; 3; 5]).
      * apply lt_custom_bool_false_5_2.
      * apply isr_skip with (x := 5) (h := 4) (t := [3]) (result := [3; 5]).
        -- apply lt_custom_bool_false_5_4.
        -- apply isr_skip with (x := 5) (h := 3) (t := []) (result := [5]).
           ++ apply lt_custom_bool_false_5_3.
           ++ apply isr_nil.
  - (* Insert 1 into [2;4;3;5] -> [1;2;4;3;5] *)
    apply isr_insert with (x := 1) (h := 2) (t := [4; 3; 5]).
    + apply lt_custom_bool_1_2.
Qed.