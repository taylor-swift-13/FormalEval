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

(* Test case: input = [[5; 4; 3; 2; 1; 2; 3; 4; 5]], output = false *)
Example test_monotonic : problem_57_spec [5; 4; 3; 2; 1; 2; 3; 4; 5] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H_inc | H_dec].
    + (* Case: Sorted Z.le (increasing) *)
      (* Fails at 5 <= 4 *)
      inversion H_inc; subst.
      match goal with
      | H: HdRel _ 5 (4 :: _) |- _ => inversion H; subst; lia
      end.
    + (* Case: Sorted Z.ge (decreasing) *)
      (* Fails at 1 >= 2 *)
      repeat match goal with
             | H: Sorted _ (_ :: _) |- _ => inversion H; subst; clear H
             end.
      match goal with
      | H: HdRel _ 1 (2 :: _) |- _ => inversion H; subst; lia
      end.
Qed.