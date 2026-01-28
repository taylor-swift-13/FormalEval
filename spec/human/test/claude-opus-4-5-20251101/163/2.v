(* 引入所需的基础库 *)
Require Import Coq.Lists.List.      (* List 定义与操作 *)
Require Import Coq.Arith.Arith.      (* 算术相关，包含 min, max, le, lt 等 *)
Require Import Coq.Sorting.Sorted.  (* Sorted 定义 *)
Require Import Coq.Lists.SetoidList.  (* NoDup 定义 *)
Require Import Lia.
Import ListNotations.

(*
  generate_integers_spec 是函数 generate_integers 的程序规约。

  - a, b: 输入的两个自然数。
  - l: 输出的结果列表。

  该规约使用一阶逻辑精确地描述了输入 a, b 与输出列表 l 之间应满足的关系。
*)
(* 输入为正整数 *)
Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (* 
    第一部分：正确性与完备性
    使用 <-> (当且仅当) 来约束列表 l 中的元素。
    它规定 l 中的每一个元素 d 都必须是处在 a 和 b 所构成的闭区间内、小于10、且为偶数的自然数。
    同时，任何满足这些条件的自然数 d 都必须在列表 l 中。
  *)
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\

  (* 
    第二部分：排序
    规定列表 l 必须是升序排列的 (非递减)。
   *)
  Sorted le l /\

  (* 
    第三部分：唯一性
    规定列表 l 中不能有重复元素。
   *)
  NoDup l.

Example test_generate_integers_10_2 :
  problem_163_spec 10 2 [2; 4; 6; 8].
Proof.
  unfold problem_163_spec.
  split; [| split].
  - (* Part 1: correctness and completeness *)
    intros d.
    simpl.
    split.
    + (* In d [2;4;6;8] -> conditions *)
      intros H.
      destruct H as [H | [H | [H | [H | H]]]].
      -- subst d. repeat split; try lia. exists 1. lia.
      -- subst d. repeat split; try lia. exists 2. lia.
      -- subst d. repeat split; try lia. exists 3. lia.
      -- subst d. repeat split; try lia. exists 4. lia.
      -- contradiction.
    + (* conditions -> In d [2;4;6;8] *)
      intros (Hmin & Hmax & Hlt10 & Heven).
      simpl in Hmin, Hmax.
      destruct Heven as [k Hk].
      subst d.
      assert (Hk_cases : k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
      destruct Hk_cases as [Hk1 | [Hk2 | [Hk3 | Hk4]]].
      -- subst k. left. reflexivity.
      -- subst k. right. left. reflexivity.
      -- subst k. right. right. left. reflexivity.
      -- subst k. right. right. right. left. reflexivity.
  - (* Part 2: sorted *)
    repeat constructor; lia.
  - (* Part 3: no duplicates *)
    constructor.
    + simpl. intros [H | [H | [H | H]]]; lia.
    + constructor.
      -- simpl. intros [H | [H | H]]; lia.
      -- constructor.
         ++ simpl. intros [H | H]; lia.
         ++ constructor.
            ** simpl. intros H; lia.
            ** constructor.
Qed.