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

(* Test case: input = [[4; 5; 3; 3; 3; 4]], output = false *)
Example test_monotonic : problem_57_spec [4%Z; 5%Z; 3%Z; 3%Z; 3%Z; 4%Z] false.
Proof.
  unfold problem_57_spec.
  split.
  - intros H. discriminate.
  - intros [H | H].
    + (* Case: Sorted Z.le *)
      (* Deconstruct Sorted Z.le [4; 5; 3; ...] *)
      inversion H as [|? ? Htail1 Hrel1]; subst.
      (* Deconstruct Sorted Z.le [5; 3; ...] *)
      inversion Htail1 as [|? ? Htail2 Hrel2]; subst.
      (* Deconstruct HdRel Z.le 5 (3 :: ...) which implies 5 <= 3 *)
      inversion Hrel2; subst.
      lia.
    + (* Case: Sorted Z.ge *)
      (* Deconstruct Sorted Z.ge [4; 5; ...] *)
      inversion H as [|? ? Htail1 Hrel1]; subst.
      (* Deconstruct HdRel Z.ge 4 (5 :: ...) which implies 4 >= 5 *)
      inversion Hrel1; subst.
      lia.
Qed.