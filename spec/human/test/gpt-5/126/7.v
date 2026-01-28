Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* 仅非负整数（nat 已满足），无额外约束 *)
Definition problem_126_pre (l : list nat) : Prop := True.

(* 程序规约 (Spec) *)
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

Example problem_126_test_case_1 :
  problem_126_spec [] true.
Proof.
  unfold problem_126_spec.
  split.
  - intros _. reflexivity.
  - intros _. constructor.
Qed.