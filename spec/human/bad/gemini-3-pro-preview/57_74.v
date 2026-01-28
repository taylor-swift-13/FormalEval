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

(* Test case: input = [[3; 1; 3; 2; 3]], output = false *)
Example test_monotonic : problem_57_spec [3; 1; 3; 2; 3] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate H.
  - intros [H | H].
    + (* Case: Sorted Z.le (increasing) *)
      inversion H; subst.
      inversion H2; subst. (* HdRel Z.le 3 (1::...) implies 3 <= 1 *)
      inversion H4; subst.
      lia.
    + (* Case: Sorted Z.ge (decreasing) *)
      inversion H; subst.
      inversion H3; subst. (* Sorted Z.ge [1; 3; 2; 3] *)
      inversion H5; subst. (* HdRel Z.ge 1 (3::...) implies 1 >= 3 *)
      inversion H7; subst.
      lia.
Qed.