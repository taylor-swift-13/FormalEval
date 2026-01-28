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

(* Test case: input = [[1; 1; 1; 1; 2; 1; 1]], output = false *)
Example test_monotonic : problem_57_spec [1; 1; 1; 1; 2; 1; 1] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate H.
  - intros [Hinc | Hdec].
    + (* Case: Sorted Z.le *)
      (* The list fails to be increasing at ... 2; 1 ... *)
      inversion Hinc as [|? ? H1 _]; subst.
      inversion H1 as [|? ? H2 _]; subst.
      inversion H2 as [|? ? H3 _]; subst.
      inversion H3 as [|? ? H4 _]; subst.
      inversion H4 as [|? ? H5 Hrel]; subst.
      inversion Hrel; subst.
      lia.
    + (* Case: Sorted Z.ge *)
      (* The list fails to be decreasing at ... 1; 2 ... *)
      inversion Hdec as [|? ? H1 _]; subst.
      inversion H1 as [|? ? H2 _]; subst.
      inversion H2 as [|? ? H3 _]; subst.
      inversion H3 as [|? ? H4 Hrel]; subst.
      inversion Hrel; subst.
      lia.
Qed.