Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

(* 仅非负整数（nat 已满足），无额外约束 *)
Definition problem_126_pre (l : list nat) : Prop := True.

(* 程序规约 (Spec) *)
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

(* Test case: input = [], output = true *)
Example problem_126_example : problem_126_spec [] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    apply Sorted_nil.
Qed.