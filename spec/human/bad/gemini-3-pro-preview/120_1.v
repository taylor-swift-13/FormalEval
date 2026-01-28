(* 引入所需的Coq库 *)
Require Import Coq.Lists.List.      (* List基本操作 *)
Require Import Coq.ZArith.ZArith.    (* 整数Z *)
Require Import Coq.Sorting.Permutation. (* Permutation定义 *)
Require Import Coq.Sorting.Sorted.      (* Sorted定义 *)
Require Import Coq.micromega.Lia.    (* 自动化整数算术证明 *)

(* 打开整数和列表的作用域以便使用相关操作符 *)
Open Scope Z_scope.
Open Scope list_scope.

(* 约束：1 <= length arr <= 1000；元素绝对值 <= 1000；0 <= k <= length arr *)
(* 使用 %nat 作用域标记来解决 length arr (nat) 和 1 (Z) 的类型不匹配问题 *)
Definition problem_120_pre (arr : list Z) (k : nat) : Prop :=
       (length arr >= 1)%nat /\ (length arr <= 1000)%nat /\
       Forall (fun z => -1000 <= z /\ z <= 1000) arr /\
       (k <= length arr)%nat.

(*
 * @brief 程序规约：top_k_spec
 * @param arr 输入的整数列表
 * @param k   需要选出的最大元素数量
 * @param res 输出的结果列表
 *
 * 这个规约断言 res 是 arr 中 k 个最大元素的有序列表。
 *)
Definition problem_120_spec (arr : list Z) (k : nat) (res : list Z) : Prop :=
  (* 1. 输出列表的长度必须为 k *)
  length res = k /\

  (* 2. 输出列表必须是升序排列的 *)
  Sorted Z.le res /\

  (* 3. 存在一个 "剩余" 列表 rest_of_arr，它包含 arr 中所有未被选入 res 的元素 *)
  (exists rest_of_arr,
    (* 3a. res 和 rest_of_arr 的组合是原始列表 arr 的一个排列组合。
           这确保了 res 中的所有元素都来自 arr，且元素的数量/重复次数正确。 *)
    Permutation (res ++ rest_of_arr) arr /\

    (* 3b. res 中的任何元素都必须大于或等于 rest_of_arr 中的任何元素。
           这确保了 res 包含的是 k 个最大的数。 *)
    (forall x y, In x res -> In y rest_of_arr -> y <= x)).

(* Test case: input = [[-3; -4; 5]; 3], output = [-4; -3; 5] *)
Example test_problem_120 : problem_120_spec [-3; -4; 5] 3 [-4; -3; 5].
Proof.
  (* 展开规约定义 *)
  unfold problem_120_spec.
  
  (* 分解为三个主要目标: 长度, 排序, 元素组成 *)
  split.
  
  (* 1. 证明长度相等 *)
  - simpl. reflexivity.

  - split.
    (* 2. 证明结果列表是排序的 *)
    + repeat constructor; simpl; try lia.

    (* 3. 证明存在剩余列表满足排列和最大值属性 *)
    + (* 因为 k=3 且原数组长度为 3，剩余列表必须为空 *)
      exists nil.
      split.
      
      (* 3a. 证明排列: [-4; -3; 5] ++ [] 是 [-3; -4; 5] 的排列 *)
      * rewrite app_nil_r. (* 简化 ++ [] *)
        (* 目标: Permutation [-4; -3; 5] [-3; -4; 5] *)
        (* 这对应于交换前两个元素，使用 Permutation_swap 定理 *)
        apply Permutation_swap.
      
      (* 3b. 证明大小关系: 对于所有 x 在 res 中，y 在 [] 中，y <= x *)
      * intros x y Hx Hy.
        (* 由于 y 必须在空列表中，这产生矛盾 *)
        inversion Hy.
Qed.