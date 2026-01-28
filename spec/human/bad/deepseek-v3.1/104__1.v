Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Program.Tactics.

Import ListNotations.

(* Helper definitions from specification *)

Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Inductive all_digits_odd_list_rel : list nat -> Prop :=
  | adolr_nil : all_digits_odd_list_rel []
  | adolr_cons : forall h t,
      is_odd_digit h ->
      all_digits_odd_list_rel t ->
      all_digits_odd_list_rel (h :: t).

Inductive nat_to_digits_rel : nat -> list nat -> Prop :=
  | ntdr_zero : nat_to_digits_rel 0 []
  | ntdr_step : forall n d rest,
      n > 0 ->
      d = n mod 10 ->
      nat_to_digits_rel (n / 10) rest ->
      nat_to_digits_rel n (d :: rest).

Inductive has_only_odd_digits_rel : nat -> Prop :=
  | hodd_base : forall n digits,
      n > 0 ->
      nat_to_digits_rel n digits ->
      all_digits_odd_list_rel digits ->
      has_only_odd_digits_rel n.

Inductive filter_odd_digits_rel : list nat -> list nat -> Prop :=
  | fodr_nil : filter_odd_digits_rel [] []
  | fodr_keep : forall h t result,
      has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) (h :: result)
  | fodr_drop : forall h t result,
      ~ has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) result.

Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
  | isr_nil : forall x, insert_sorted_rel x [] [x]
  | isr_insert : forall x h t,
      (x <= h)%nat ->
      insert_sorted_rel x (h :: t) (x :: h :: t)
  | isr_skip : forall x h t result,
      (x > h)%nat ->
      insert_sorted_rel x t result ->
      insert_sorted_rel x (h :: t) (h :: result).

Inductive sort_list_rel : list nat -> list nat -> Prop :=
  | slr_nil : sort_list_rel [] []
  | slr_cons : forall h t sorted_tail result,
      sort_list_rel t sorted_tail ->
      insert_sorted_rel h sorted_tail result ->
      sort_list_rel (h :: t) result.

Definition problem_104_spec (x y : list nat) : Prop :=
  (forall n, In n x -> n > 0) /\
  exists filtered,
    filter_odd_digits_rel x filtered /\
    sort_list_rel filtered y.

(* Helper lemmas *)

Lemma gt_0_1 : 1 > 0. Proof. auto with arith. Qed.
Lemma gt_0_3 : 3 > 0. Proof. auto with arith. Qed.
Lemma gt_0_15 : 15 > 0. Proof. auto with arith. Qed.
Lemma gt_0_33 : 33 > 0. Proof. auto with arith. Qed.
Lemma gt_0_1422 : 1422 > 0. Proof. auto with arith. Qed.

Lemma le_1_15 : (1 <= 15)%nat. Proof. auto with arith. Qed.
Lemma le_15_33 : (15 <= 33)%nat. Proof. auto with arith. Qed.
Lemma gt_33_1 : (33 > 1)%nat. Proof. auto with arith. Qed.
Lemma gt_33_15 : (33 > 15)%nat. Proof. auto with arith. Qed.
Lemma gt_15_1 : (15 > 1)%nat. Proof. auto with arith. Qed.

Lemma has_only_odd_digits_1 : has_only_odd_digits_rel 1.
Proof.
  refine (hodd_base 1 [1] _ _ _).
  - apply gt_0_1.
  - refine (ntdr_step 1 1 [] _ _ _).
    + apply gt_0_1.
    + reflexivity.
    + apply ntdr_zero.
  - apply adolr_cons.
    + left. reflexivity.
    + apply adolr_nil.
Qed.

Lemma has_only_odd_digits_15 : has_only_odd_digits_rel 15.
Proof.
  refine (hodd_base 15 [5; 1] _ _ _).
  - apply gt_0_15.
  - refine (ntdr_step 15 5 [1] _ _ _).
    + apply gt_0_15.
    + reflexivity.
    + refine (ntdr_step 1 1 [] _ _ _).
      * apply gt_0_1.
      * reflexivity.
      * apply ntdr_zero.
  - apply adolr_cons.
    + right. right. left. reflexivity.
    + apply adolr_cons.
      * left. reflexivity.
      * apply adolr_nil.
Qed.

Lemma has_only_odd_digits_33 : has_only_odd_digits_rel 33.
Proof.
  refine (hodd_base 33 [3; 3] _ _ _).
  - apply gt_0_33.
  - refine (ntdr_step 33 3 [3] _ _ _).
    + apply gt_0_33.
    + reflexivity.
    + refine (ntdr_step 3 3 [] _ _ _).
      * apply gt_0_3.
      * reflexivity.
      * apply ntdr_zero.
  - apply adolr_cons.
    + right. left. reflexivity.
    + apply adolr_cons.
      * right. left. reflexivity.
      * apply adolr_nil.
Qed.

Lemma not_has_only_odd_digits_1422 : ~ has_only_odd_digits_rel 1422.
Proof.
  intro H.
  inversion H as [n digits Hpos Hdigits Hodd].
  inversion Hdigits as [|n' d rest Hpos' Hd Hrest].
  - discriminate.
  - inversion Hrest as [|n'' d' rest' Hpos'' Hd' Hrest'].
    + discriminate.
    + inversion Hrest' as [|n''' d'' rest'' Hpos''' Hd'' Hrest''].
      * discriminate.
      * inversion Hrest'' as [|n'''' d''' rest''' Hpos'''' Hd''' Hrest'''].
        { discriminate. }
        inversion Hodd as [|h t Hh Ht].
        inversion Ht as [|h' t' Hh' Ht'].
        inversion Ht' as [|h'' t'' Hh'' Ht''].
        inversion Ht'' as [|h''' t''' Hh''' Ht'''].
        inversion Hh'''.
        all: try discriminate.
Qed.

Lemma insert_sorted_1_nil : insert_sorted_rel 1 [] [1].
Proof.
  apply isr_nil.
Qed.

Lemma insert_sorted_15_1 : insert_sorted_rel 15 [1] [1; 15].
Proof.
  apply isr_skip.
  - apply gt_15_1.
  - apply isr_nil.
Qed.

Lemma insert_sorted_33_1_15 : insert_sorted_rel 33 [1; 15] [1; 15; 33].
Proof.
  apply isr_skip.
  - apply gt_33_1.
  - apply isr_skip.
    + apply gt_33_15.
    + apply isr_nil.
Qed.

Lemma sort_list_nil : sort_list_rel [] [].
Proof.
  apply slr_nil.
Qed.

Lemma sort_list_1 : sort_list_rel [1] [1].
Proof.
  refine (slr_cons 1 [] [] _ _).
  - apply slr_nil.
  - apply isr_nil.
Qed.

Lemma sort_list_1_15 : sort_list_rel [15; 1] [1; 15].
Proof.
  refine (slr_cons 15 [1] [1; 15] _ _).
  - apply sort_list_1.
  - apply insert_sorted_15_1.
Qed.

Lemma sort_list_33_1_15 : sort_list_rel [33; 15; 1] [1; 15; 33].
Proof.
  refine (slr_cons 33 [15; 1] [1; 15; 33] _ _).
  - apply sort_list_1_15.
  - apply insert_sorted_33_1_15.
Qed.

Lemma filter_odd_digits_15_33_1422_1 : 
  filter_odd_digits_rel [15; 33; 1422; 1] [1; 15; 33].
Proof.
  refine (fodr_keep 15 [33; 1422; 1] [15; 33] _ _).
  - apply has_only_odd_digits_15.
  - refine (fodr_keep 33 [1422; 1] [33] _ _).
    + apply has_only_odd_digits_33.
    + refine (fodr_drop 1422 [1] [] _ _).
      * apply not_has_only_odd_digits_1422.
      + refine (fodr_keep 1 [] [] _ _).
        * apply has_only_odd_digits_1.
        * apply fodr_nil.
Qed.

(* Main proof *)

Example test_case_104 : problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  split.
  - intros n H.
    destruct H as [H|H].
    + apply gt_0_15.
    + destruct H as [H|H].
      * apply gt_0_33.
      * destruct H as [H|H].
        { apply gt_0_1422. }
        { inversion H. apply gt_0_1. }
  - exists [1; 15; 33].
    split.
    + apply filter_odd_digits_15_33_1422_1.
    + apply sort_list_33_1_15.
Qed.