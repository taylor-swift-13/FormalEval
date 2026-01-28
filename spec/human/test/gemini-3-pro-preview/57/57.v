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

(* Test case: input = [[1; 1; 1; 2; 2; 1; 1]], output = false *)
Example test_monotonic : problem_57_spec [1; 1; 1; 2; 2; 1; 1] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + (* Prove ~ Sorted Z.le [1; 1; 1; 2; 2; 1; 1] *)
      repeat match goal with
      | H: Sorted _ (_ :: _) |- _ => inversion H; subst; clear H
      | H: HdRel _ _ (_ :: _) |- _ => inversion H; subst; clear H
      end.
      (* Leads to 2 <= 1 constraint which is false *)
      lia.
    + (* Prove ~ Sorted Z.ge [1; 1; 1; 2; 2; 1; 1] *)
      repeat match goal with
      | H: Sorted _ (_ :: _) |- _ => inversion H; subst; clear H
      | H: HdRel _ _ (_ :: _) |- _ => inversion H; subst; clear H
      end.
      (* Leads to 1 >= 2 constraint which is false *)
      lia.
Qed.