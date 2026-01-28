(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znat.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(* 定义一个函数来计算整数列表的和 *)
Definition list_sum (l : list Z) : Z :=
  fold_left Z.add l 0.

(* nums 非空 *)
Definition problem_114_pre (nums : list Z) : Prop := nums <> [].

(* 定义一个规约来描述最小子数组和的属性 *)
Definition problem_114_spec (nums : list Z) (min_sum : Z) : Prop :=
  (* 1. 存在性 (Existence): 必须存在一个非空子数组，其和等于 min_sum *)
  (exists sub_array,
    sub_array <> [] /\
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) /\
    list_sum sub_array = min_sum)
  /\
  (* 2. 最小性 (Minimality): 对于所有非空的子数组，它们的和都必须大于或等于 min_sum *)
  (forall sub_array,
    sub_array <> [] ->
    (exists prefix suffix, nums = prefix ++ sub_array ++ suffix) ->
    min_sum <= list_sum sub_array).

Lemma Forall_app_inv {A} (P : A -> Prop) (l1 l2 : list A) :
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros l2 H.
  - simpl in H. split; [constructor|assumption].
  - simpl in H. inversion H; subst.
    specialize (IH l2 H3). destruct IH as [H_l1 H_l2].
    split; [constructor; [assumption|assumption] | assumption].
Qed.

Lemma fold_left_add_lower_bound :
  forall l, Forall (fun x : Z => 1 <= x) l ->
  forall acc, acc + Z.of_nat (length l) <= fold_left Z.add l acc.
Proof.
  intros l Hf.
  induction Hf as [|x l Hx Htl IH]; intros acc; simpl.
  - lia.
  - rewrite Nat2Z.inj_succ.
    assert (H1 : acc + (Z.of_nat (length l) + 1) <= acc + x + Z.of_nat (length l)) by lia.
    specialize (IH (acc + x)).
    eapply Z.le_trans; [exact H1|].
    replace (acc + x + Z.of_nat (length l)) with ((acc + x) + Z.of_nat (length l)) by lia.
    exact IH.
Qed.

Lemma list_sum_ge_length_ge1 : forall l,
  Forall (fun x : Z => 1 <= x) l -> Z.of_nat (length l) <= list_sum l.
Proof.
  intros l Hf.
  unfold list_sum. specialize (fold_left_add_lower_bound l Hf 0) as Hbound.
  lia.
Qed.

Example problem_114_example_1 :
  problem_114_spec [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z] 1%Z.
Proof.
  split.
  - exists [1%Z]. split.
    + discriminate.
    + split.
      * exists [2%Z; 3%Z; 4%Z]. exists [2%Z; 4%Z]. reflexivity.
      * simpl. lia.
  - intros sub_array Hne [prefix [suffix Heq]].
    assert (HForall_nums: Forall (fun x => 1 <= x) [2%Z; 3%Z; 4%Z; 1%Z; 2%Z; 4%Z]).
    { repeat constructor; lia. }
    rewrite Heq in HForall_nums.
    apply Forall_app_inv in HForall_nums as [Hpre Hrest].
    apply Forall_app_inv in Hrest as [Hsub Hsuf].
    pose proof (list_sum_ge_length_ge1 sub_array Hsub) as Hlen_bound.
    assert (1 <= Z.of_nat (length sub_array)) as Hlen_ge1.
    { destruct sub_array as [|x xs]; [contradiction|simpl; rewrite Nat2Z.inj_succ; lia]. }
    eapply Z.le_trans; [exact Hlen_ge1|exact Hlen_bound].
Qed.