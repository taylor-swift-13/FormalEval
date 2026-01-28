(* 引入所需的库 *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
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

Example problem_114_test_case_1 :
  problem_114_spec [2; 3; 4; 1; 2; 4] 1.
Proof.
  unfold problem_114_spec.
  split.
  - exists [1].
    split.
    + simpl; intros H. inversion H.
    + exists [2; 3; 4], [2; 4]. split.
      * simpl. reflexivity.
      * unfold list_sum. simpl. lia.
  - intros sub_array Hnonempty [prefix [suffix Heq]].
    (* We need to demonstrate that the sum of any non-empty subarray is >= 1 *)
    assert (Hsum: list_sum sub_array >= 1).
    { destruct sub_array as [|a sub_array'].
      - simpl in Hnonempty. contradiction.
      - simpl. unfold list_sum. simpl in Heq.
        assert (Hprefix: exists prefix', prefix = prefix' ++ [a]).
        { exists (firstn (length prefix - 1) prefix).
          rewrite firstn_app, firstn_all2 by lia.
          rewrite app_comm_cons.
          rewrite <- Heq.
          rewrite app_assoc. reflexivity. }
        destruct Hprefix as [prefix' Hprefix].
        rewrite Hprefix in Heq.
        simpl in Heq.
        rewrite <- app_assoc in Heq.
        apply app_inj_tail in Heq as [H0 H1].
        specialize (app_eq_nil _ _ H0) as [_ H2].
        rewrite H2 in *.
        simpl in H1.
        subst.
        unfold list_sum. simpl. lia. }
    exact Hsum.
Qed.