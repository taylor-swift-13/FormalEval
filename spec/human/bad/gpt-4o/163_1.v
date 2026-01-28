(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Import ListNotations.

(* 判断一个数是否为偶数的布尔函数 *)
Definition is_even (n : nat) : bool :=
  Nat.even n.

(* 在给定区间内生成偶数 *)
Definition generate_integers (a b : nat) : list nat :=
  filter is_even (seq (min a b) (S (max a b - min a b))).

(* 规格定义 *)
Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

(* 证明 generate_integers 满足规格 *)
Lemma generate_integers_correct :
  forall a b, a > 0 /\ b > 0 ->
  problem_163_spec a b (generate_integers a b).
Proof.
  intros a b [Ha Hb].
  unfold problem_163_spec, generate_integers.
  split.
  - intros d. split; intros H.
    + apply filter_In in H. destruct H as [Hseq Heven].
      apply seq_In in Hseq. split; [| split; [| split]]; try lia.
      apply Nat.even_spec. now apply Heven.
    + apply filter_In. destruct H as [Hmin [Hmax [Hlt Heven]]].
      split.
      * apply seq_In. lia.
      * apply Nat.even_spec. assumption.
  - split.
    + apply filter_sorted. apply seq_Sorted. apply Nat.le_min_l.
    + apply NoDup_filter. apply seq_NoDup.
Qed.

Example test_generate_integers : generate_integers 2 10 = [2; 4; 6; 8].
Proof.
  unfold generate_integers. simpl.
  assert (seq (min 2 10) (S (max 2 10 - min 2 10)) = [2; 3; 4; 5; 6; 7; 8; 9; 10]).
  {
    simpl. reflexivity.
  }
  rewrite H.
  simpl.
  reflexivity.
Qed.