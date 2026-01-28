Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(*
 * monotonic 函数的最终程序规约。
 * 输入列表 l 和输出布尔值 b，它们之间的关系是：
 * b 为 true 当且仅当 l 是单调递增或单调递减的。
 *)
(* Pre: no special constraints for `monotonic` on integer lists *)
Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

(* Test case: input = [[5; 1; -10; 7; -9; 1; 2; 5]], output = false *)
Example test_monotonic : problem_57_spec [5; 1; -10; 7; -9; 1; 2; 5] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate H.
  - intros [H | H].
    + (* Case Sorted Z.le: 5 <= 1 is false *)
      inversion H as [|? ? H_tail1 H_hd1]; subst.
      inversion H_hd1; subst.
      lia.
    + (* Case Sorted Z.ge: -10 >= 7 is false *)
      inversion H as [|? ? H_tail1 H_hd1]; subst.
      inversion H_tail1 as [|? ? H_tail2 H_hd2]; subst.
      inversion H_tail2 as [|? ? H_tail3 H_hd3]; subst.
      inversion H_hd3; subst.
      lia.
Qed.