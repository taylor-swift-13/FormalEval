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

(* Test case: input = [[5; 1; -7; -9; 1; 5]], output = false *)
Example test_monotonic : problem_57_spec [5; 1; -7; -9; 1; 5] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate H.
  - intros [H_inc | H_dec].
    + (* Case: Sorted Z.le [5; 1; ...] *)
      inversion H_inc as [| ? ? H_s1 H_r1]; subst.
      inversion H_r1; subst. (* HdRel 5 (1::...) implies 5 <= 1 *)
      lia.
    + (* Case: Sorted Z.ge [5; 1; -7; -9; 1; 5] *)
      inversion H_dec as [| ? ? H_s1 H_r1]; subst. (* 5 >= 1 *)
      inversion H_s1 as [| ? ? H_s2 H_r2]; subst. (* 1 >= -7 *)
      inversion H_s2 as [| ? ? H_s3 H_r3]; subst. (* -7 >= -9 *)
      inversion H_s3 as [| ? ? H_s4 H_r4]; subst. (* -9 >= 1 *)
      inversion H_r4; subst. (* HdRel -9 (1::...) implies -9 >= 1 *)
      lia.
Qed.