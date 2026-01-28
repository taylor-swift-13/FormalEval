(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia. (* Use Lia instead of Omega *)

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

Example test_case_104 :
  problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  unfold problem_104_spec.
  split.
  - intros n H. repeat (destruct H as [H | H]; subst; try lia).
  - exists [1; 15; 33].
    split.
    + apply fodr_keep.
      * apply hodd_base with (digits := [1]).
        -- lia.
        -- apply ntdr_step with (d := 1) (rest := []); try lia.
           ++ reflexivity.
           ++ apply ntdr_zero.
        -- apply adolr_cons; [left; reflexivity | apply adolr_nil].
      * apply fodr_keep.
        -- apply hodd_base with (digits := [3; 3]).
           ++ lia.
           ++ apply ntdr_step with (d := 3) (rest := [3]); try lia.
              ** reflexivity.
              ** apply ntdr_step with (d := 3) (rest := []); try lia.
                 +++ reflexivity.
                 +++ apply ntdr_zero.
           ++ apply adolr_cons; [right; left; reflexivity |].
              apply adolr_cons; [right; left; reflexivity | apply adolr_nil].
        -- apply fodr_drop.
           ++ intro H. inversion H. inversion H2. lia.
           ++ apply fodr_keep.
              ** apply hodd_base with (digits := [1]).
                 --- lia.
                 --- apply ntdr_step with (d := 1) (rest := []); try lia.
                     +++ reflexivity.
                     +++ apply ntdr_zero.
                 --- apply adolr_cons; [left; reflexivity | apply adolr_nil].
              ** apply fodr_nil.
    + apply slr_cons with (sorted_tail := [15; 33]).
      * apply slr_cons with (sorted_tail := [33]).
        -- apply slr_cons with (sorted_tail := []).
           ++ apply slr_nil.
           ++ apply isr_nil.
        -- apply isr_insert; lia.
      * apply isr_insert; lia.
Qed.