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

(* Test case: input = [[3; 2; 6; 1; 7; 2]], output = false *)
Example test_monotonic : problem_57_spec [3; 2; 6; 1; 7; 2] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + (* Case Sorted Z.le: 3 <= 2 is false *)
      inversion H as [|? ? H_tl H_hd]; subst.
      inversion H_hd; subst.
      lia.
    + (* Case Sorted Z.ge: 2 >= 6 is false *)
      inversion H as [|? ? H_tl H_hd]; subst.
      inversion H_tl as [|? ? H_tl' H_hd']; subst.
      inversion H_hd'; subst.
      lia.
Qed.