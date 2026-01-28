Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Sorting.Sorted.
Import ListNotations.

(* 仅非负整数（nat 已满足），无额外约束 *)
Definition problem_126_pre (l : list nat) : Prop := True.

(* 程序规约 (Spec) *)
Definition problem_126_spec (l : list nat) (b : bool) : Prop :=
  Sorted Nat.lt l <-> b = true.

(* Test case: input = [5], output = true *)
(* We need to prove that Sorted Nat.lt [5] <-> true = true *)
Example problem_126_example : problem_126_spec [5] true.
Proof.
  unfold problem_126_spec.
  split.
  - (* Sorted Nat.lt [5] -> true = true *)
    intros _. reflexivity.
  - (* true = true -> Sorted Nat.lt [5] *)
    intros _.
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
Qed.