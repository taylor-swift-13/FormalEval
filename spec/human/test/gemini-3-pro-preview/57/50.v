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

(* Test case: input = [[3; 6; 2; 6; 7; 2]], output = false *)
Example test_monotonic : problem_57_spec [3; 6; 2; 6; 7; 2] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + (* Case: Sorted Z.le *)
      (* 3 <= 6 (ok), 6 <= 2 (fail) *)
      inversion H as [| x1 l1 Htl1 Hhd1]; subst.
      inversion Htl1 as [| x2 l2 Htl2 Hhd2]; subst.
      inversion Hhd2; subst.
      lia.
    + (* Case: Sorted Z.ge *)
      (* 3 >= 6 (fail) *)
      inversion H as [| x1 l1 Htl1 Hhd1]; subst.
      inversion Hhd1; subst.
      lia.
Qed.