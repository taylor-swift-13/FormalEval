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

(* Test case: input = [[5; 1; -10; -7; -9; 1; 2; 5]], output = false *)
Example test_monotonic : problem_57_spec [5; 1; -10; -7; -9; 1; 2; 5] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. inversion H.
  - intros [H | H].
    + (* Case: Sorted Z.le. Fails at 5 <= 1 *)
      inversion H as [|? ? H_tail H_rel]; subst.
      inversion H_rel; subst.
      lia.
    + (* Case: Sorted Z.ge. Fails at -10 >= -7 *)
      inversion H as [|? ? H1 H_rel1]; subst. (* 5 :: ... *)
      inversion H1 as [|? ? H2 H_rel2]; subst. (* 1 :: ... *)
      inversion H2 as [|? ? H3 H_rel3]; subst. (* -10 :: ... *)
      inversion H_rel3; subst. (* HdRel -10 (-7 :: ...) *)
      lia.
Qed.