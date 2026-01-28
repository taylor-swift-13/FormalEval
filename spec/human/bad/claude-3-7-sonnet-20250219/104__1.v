Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Lia.

Import ListNotations.

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

(* Lemmas for nat_to_digits_rel and all_digits_odd_list_rel *)

Lemma nat_to_digits_rel_1 : nat_to_digits_rel 1 [1].
Proof.
  apply ntdr_step with (d := 1) (rest := []).
  - lia.
  - reflexivity.
  - apply ntdr_zero.
Qed.

Lemma all_digits_odd_list_rel_1 : all_digits_odd_list_rel [1].
Proof.
  constructor.
  - left; reflexivity.
  - constructor.
Qed.

Lemma has_only_odd_digits_rel_1 : has_only_odd_digits_rel 1.
Proof.
  apply hodd_base with (digits := [1]).
  - lia.
  - apply nat_to_digits_rel_1.
  - apply all_digits_odd_list_rel_1.
Qed.

Lemma nat_to_digits_rel_5 : nat_to_digits_rel 5 [5].
Proof.
  apply ntdr_step with (d := 5) (rest := []).
  - lia.
  - reflexivity.
  - apply ntdr_zero.
Qed.

Lemma nat_to_digits_rel_15 : nat_to_digits_rel 15 [5;1].
Proof.
  apply ntdr_step with (d := 5) (rest := [1]).
  - lia.
  - reflexivity.
  - apply nat_to_digits_rel_1.
Qed.

Lemma all_digits_odd_list_rel_15 : all_digits_odd_list_rel [5;1].
Proof.
  constructor.
  - right; right; left; reflexivity.
  - constructor.
    + left; reflexivity.
    + constructor.
Qed.

Lemma has_only_odd_digits_rel_15 : has_only_odd_digits_rel 15.
Proof.
  apply hodd_base with (digits := [5;1]).
  - lia.
  - apply nat_to_digits_rel_15.
  - apply all_digits_odd_list_rel_15.
Qed.

Lemma nat_to_digits_rel_3 : nat_to_digits_rel 3 [3].
Proof.
  apply ntdr_step with (d := 3) (rest := []).
  - lia.
  - reflexivity.
  - apply ntdr_zero.
Qed.

Lemma all_digits_odd_list_rel_3 : all_digits_odd_list_rel [3].
Proof.
  constructor.
  - right; left; reflexivity.
  - constructor.
Qed.

Lemma has_only_odd_digits_rel_3 : has_only_odd_digits_rel 3.
Proof.
  apply hodd_base with (digits := [3]).
  - lia.
  - apply nat_to_digits_rel_3.
  - apply all_digits_odd_list_rel_3.
Qed.

Lemma nat_to_digits_rel_33 : nat_to_digits_rel 33 [3;3].
Proof.
  apply ntdr_step with (d := 3) (rest := [3]).
  - lia.
  - reflexivity.
  - apply nat_to_digits_rel_3.
Qed.

Lemma all_digits_odd_list_rel_33 : all_digits_odd_list_rel [3;3].
Proof.
  constructor.
  - right; left; reflexivity.
  - apply all_digits_odd_list_rel_3.
Qed.

Lemma has_only_odd_digits_rel_33 : has_only_odd_digits_rel 33.
Proof.
  apply hodd_base with (digits := [3;3]).
  - lia.
  - apply nat_to_digits_rel_33.
  - apply all_digits_odd_list_rel_33.
Qed.

(* For 1422, digits include even digits, so ~ has_only_odd_digits_rel *)

Lemma nat_to_digits_rel_1422 : nat_to_digits_rel 1422 [2;2;4;1].
Proof.
  apply ntdr_step with (d := 2) (rest := [2;4;1]); lia; reflexivity.
  apply ntdr_step with (d := 2) (rest := [4;1]); lia; reflexivity.
  apply ntdr_step with (d := 4) (rest := [1]); lia; reflexivity.
  apply nat_to_digits_rel_1.
Qed.

Lemma has_only_odd_digits_rel_1422_false : ~ has_only_odd_digits_rel 1422.
Proof.
  intro H.
  inversion H as [n digits Hpos Hnat Hall].
  subst.
  inversion Hall; subst.
  destruct H2 as [Hodd|[Hodd|[Hodd|[Hodd|Hodd]]]]; discriminate.
Qed.

(* For 10 digits [0;1], 0 is even *)

Lemma nat_to_digits_rel_10 : nat_to_digits_rel 10 [0;1].
Proof.
  apply ntdr_step with (d := 0) (rest := [1]); lia; reflexivity.
  apply nat_to_digits_rel_1.
Qed.

Lemma has_only_odd_digits_rel_10_false : ~ has_only_odd_digits_rel 10.
Proof.
  intro H.
  inversion H as [n digits Hpos Hnat Hall].
  subst.
  inversion Hall; subst.
  destruct H2 as [Hodd|[Hodd|[Hodd|[Hodd|Hodd]]]]; discriminate.
Qed.

(* Filtering lemma for [15;33;1422;1] to [15;33;1] *)

Lemma filter_odd_digits_rel_15331421_1331 :
  filter_odd_digits_rel [15;33;1422;1] [15;33;1].
Proof.
  apply fodr_keep.
  - apply has_only_odd_digits_rel_15.
  - apply fodr_keep.
    + apply has_only_odd_digits_rel_33.
    + apply fodr_drop.
      * apply has_only_odd_digits_rel_1422_false.
      * apply fodr_keep.
        -- apply has_only_odd_digits_rel_1.
        -- apply fodr_nil.
Qed.

(* Insert lemmas *)

Lemma insert_sorted_rel_1_nil : insert_sorted_rel 1 [] [1].
Proof. apply isr_nil. Qed.

Lemma insert_sorted_rel_15_1 : insert_sorted_rel 15 [1] [1;15].
Proof.
  apply isr_skip; lia; apply isr_nil.
Qed.

Lemma insert_sorted_rel_33_1_15 : insert_sorted_rel 33 [1;15] [1;15;33].
Proof.
  apply isr_skip; lia.
  apply insert_sorted_rel_15_1.
Qed.

(* Sort [1;15;33] *)

Lemma sort_list_rel_1_15_33 : sort_list_rel [1;15;33] [1;15;33].
Proof.
  apply slr_cons with (sorted_tail := [15;33]).
  - apply slr_cons with (sorted_tail := [33]).
    + apply slr_cons with (sorted_tail := []).
      * apply slr_nil.
      * apply isr_nil.
    + apply insert_sorted_rel_15_33.
  - apply insert_sorted_rel_1_15_33.
Admitted.

(* Easier to prove full sorting here with an alternative direct proof *)

Lemma insert_sorted_rel_15_33 : insert_sorted_rel 15 [33] [15;33].
Proof.
  apply isr_insert; lia.
Qed.

Lemma insert_sorted_rel_1_15_33 : insert_sorted_rel 1 [15;33] [1;15;33].
Proof.
  apply isr_insert; lia.
Qed.

Lemma sort_list_rel_full : sort_list_rel [15;33;1] [1;15;33].
Proof.
  apply slr_cons with (sorted_tail := sorted_tail).
  - (* Sort [33;1] *)
    apply slr_cons with (sorted_tail := [1]).
    + apply slr_cons with (sorted_tail := []).
      * apply slr_nil.
      * apply insert_sorted_rel_1_nil.
    + apply isr_skip; lia; apply insert_sorted_rel_1_nil.
  - apply insert_sorted_rel_15_33.
Qed.

Example problem_104_example :
  problem_104_spec [15;33;1422;1] [1;15;33].
Proof.
  split.
  - intros n H; simpl in H.
    destruct H as [->|[->|[->|[->|[]]]]]; lia.
  - exists [15;33;1].
    split.
    + apply filter_odd_digits_rel_15331421_1331.
    + apply sort_list_rel_full.
Qed.