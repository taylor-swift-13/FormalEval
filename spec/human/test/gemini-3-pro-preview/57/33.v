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

(* Test case: input = [[10; -11; 9; 8; 7; 6; 6]], output = false *)
Example test_monotonic : problem_57_spec [10; -11; 9; 8; 7; 6; 6] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + (* Case: Sorted Z.le [10; -11; ...] *)
      inversion H; subst.
      (* HdRel 10 (-11::...) implies 10 <= -11 which is false *)
      match goal with H: HdRel _ _ _ |- _ => inversion H; subst end.
      lia.
    + (* Case: Sorted Z.ge [10; -11; 9; ...] *)
      inversion H; subst.
      (* Decompose to find the violation at -11 vs 9 *)
      match goal with H: Sorted _ (_ :: _) |- _ => inversion H; subst end.
      match goal with H: HdRel _ (-11) (9 :: _) |- _ => inversion H; subst end.
      lia.
Qed.