Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold problem_43_spec.
  split.
  - (* Forward direction: existence implies true, but output is false *)
    intros [i [j [Hneq [Hi [Hj Hsum]]]]].
    simpl in Hi, Hj.
    (* We need to show this leads to a contradiction *)
    (* The list is [1; 3; 5; 0], length is 4 *)
    (* We need to check all possible pairs *)
    destruct i as [|[|[|[|i']]]]; destruct j as [|[|[|[|j']]]];
    try lia; (* eliminate cases where i >= 4 or j >= 4 *)
    try (exfalso; apply Hneq; reflexivity); (* eliminate cases where i = j *)
    simpl in Hsum; lia. (* check that no valid pair sums to 0 *)
  - (* Backward direction: true implies existence, but output is false *)
    intros H.
    discriminate H.
Qed.