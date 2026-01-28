(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
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

(* Helper lemmas *)

(* Lemma to handle fold_left associativity with addition *)
Lemma fold_left_Zadd_assoc : forall l acc,
  fold_left Z.add l acc = acc + fold_left Z.add l 0.
Proof.
  induction l as [|x xs IH]; intros acc.
  - simpl. lia.
  - simpl. rewrite IH. rewrite (IH x). lia.
Qed.

(* Simplification of list_sum for cons *)
Lemma list_sum_cons : forall x xs,
  list_sum (x :: xs) = x + list_sum xs.
Proof.
  intros. unfold list_sum. simpl.
  apply fold_left_Zadd_assoc.
Qed.

(* If all elements are non-negative, the sum is non-negative *)
Lemma list_sum_nonneg : forall l,
  Forall (fun x => 0 <= x) l -> 0 <= list_sum l.
Proof.
  induction l; intros H.
  - unfold list_sum. simpl. lia.
  - rewrite list_sum_cons.
    inversion H; subst.
    apply IHl in H3.
    lia.
Qed.

(* If all elements are >= m (where m >= 0) and list is not empty, sum is >= m *)
Lemma list_sum_ge_min : forall l m,
  l <> [] ->
  Forall (fun x => m <= x) l ->
  0 <= m ->
  m <= list_sum l.
Proof.
  intros l m Hnotnil Hall Hmpos.
  destruct l as [|x xs].
  - contradiction.
  - rewrite list_sum_cons.
    inversion Hall as [|? ? Hx Hxs]; subst.
    assert (0 <= list_sum xs).
    {
      apply list_sum_nonneg.
      eapply Forall_impl; eauto.
      intros a Ha. lia.
    }
    lia.
Qed.

(* Main proof for the test case *)
Example test_problem_114_example : problem_114_spec [2; 3; 4; 1; 2; 4] 1.
Proof.
  unfold problem_114_spec.
  split.
  
  (* Part 1: Existence *)
  - exists [1].
    split.
    + (* sub_array <> [] *)
      discriminate.
    + split.
      * (* exists prefix suffix ... *)
        exists [2; 3; 4], [2; 4].
        reflexivity.
      * (* list_sum sub_array = 1 *)
        vm_compute. reflexivity.

  (* Part 2: Minimality *)
  - intros sub_array H_non_empty [prefix [suffix H_eq]].
    
    (* Prove that all elements in the input list are >= 1 *)
    assert (H_all_ge_1: Forall (fun x => 1 <= x) [2; 3; 4; 1; 2; 4]).
    { repeat constructor; lia. }
    
    (* Consequently, all elements in the sub_array are >= 1 *)
    rewrite H_eq in H_all_ge_1.
    apply Forall_app in H_all_ge_1. destruct H_all_ge_1 as [_ H_temp].
    apply Forall_app in H_temp. destruct H_temp as [H_sub_ge_1 _].
    
    (* Apply the helper lemma *)
    apply list_sum_ge_min.
    + assumption.
    + assumption.
    + lia.
Qed.