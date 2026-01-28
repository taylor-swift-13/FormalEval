(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Import ListNotations.

(* 辅助定义：判断单个数字是否为奇数 *)
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

Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list nat) : Prop :=
  (forall n, In n x -> n > 0) /\
  exists filtered,
    filter_odd_digits_rel x filtered /\
    sort_list_rel filtered y.

(* Helper lemmas *)

Lemma is_odd_digit_1 : is_odd_digit 1.
Proof. unfold is_odd_digit. left. reflexivity. Qed.

Lemma is_odd_digit_3 : is_odd_digit 3.
Proof. unfold is_odd_digit. right. left. reflexivity. Qed.

Lemma is_odd_digit_5 : is_odd_digit 5.
Proof. unfold is_odd_digit. right. right. left. reflexivity. Qed.

Lemma has_only_odd_digits_1 : has_only_odd_digits_rel 1.
Proof.
  apply (hodd_base 1 [1]).
  - lia.
  - apply ntdr_step with (d := 1) (rest := []).
    + lia.
    + reflexivity.
    + apply ntdr_zero.
  - apply adolr_cons.
    + apply is_odd_digit_1.
    + apply adolr_nil.
Qed.

Lemma has_only_odd_digits_15 : has_only_odd_digits_rel 15.
Proof.
  apply (hodd_base 15 [5; 1]).
  - lia.
  - apply ntdr_step with (d := 5) (rest := [1]).
    + lia.
    + reflexivity.
    + apply ntdr_step with (d := 1) (rest := []).
      * lia.
      * reflexivity.
      * apply ntdr_zero.
  - apply adolr_cons.
    + apply is_odd_digit_5.
    + apply adolr_cons.
      * apply is_odd_digit_1.
      * apply adolr_nil.
Qed.

Lemma has_only_odd_digits_33 : has_only_odd_digits_rel 33.
Proof.
  apply (hodd_base 33 [3; 3]).
  - lia.
  - apply ntdr_step with (d := 3) (rest := [3]).
    + lia.
    + reflexivity.
    + apply ntdr_step with (d := 3) (rest := []).
      * lia.
      * reflexivity.
      * apply ntdr_zero.
  - apply adolr_cons.
    + apply is_odd_digit_3.
    + apply adolr_cons.
      * apply is_odd_digit_3.
      * apply adolr_nil.
Qed.

Lemma not_is_odd_digit_2 : ~ is_odd_digit 2.
Proof.
  unfold is_odd_digit. intro H.
  destruct H as [H|[H|[H|[H|H]]]]; discriminate.
Qed.

Lemma not_has_only_odd_digits_1422 : ~ has_only_odd_digits_rel 1422.
Proof.
  intro H.
  inversion H; subst.
  inversion H1; subst.
  - lia.
  - assert (Hmod: 1422 mod 10 = 2) by reflexivity.
    rewrite Hmod in H4.
    inversion H2; subst.
    apply not_is_odd_digit_2. exact H5.
Qed.

Example problem_104_test :
  problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  unfold problem_104_spec.
  split.
  - intros n Hin.
    simpl in Hin.
    destruct Hin as [H|[H|[H|[H|H]]]].
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + subst. lia.
    + contradiction.
  - exists [15; 33; 1].
    split.
    + apply fodr_keep.
      * apply has_only_odd_digits_15.
      * apply fodr_keep.
        -- apply has_only_odd_digits_33.
        -- apply fodr_drop.
           ++ apply not_has_only_odd_digits_1422.
           ++ apply fodr_keep.
              ** apply has_only_odd_digits_1.
              ** apply fodr_nil.
    + apply slr_cons with (sorted_tail := [1; 33]).
      * apply slr_cons with (sorted_tail := [1]).
        -- apply slr_cons with (sorted_tail := []).
           ++ apply slr_nil.
           ++ apply isr_nil.
        -- apply isr_skip.
           ++ lia.
           ++ apply isr_nil.
      * apply isr_skip.
        -- lia.
        -- apply isr_insert.
           lia.
Qed.