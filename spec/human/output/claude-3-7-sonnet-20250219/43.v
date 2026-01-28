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
  - intros [i [j [H1 [H2 [H3 H4]]]]].
    simpl in H2, H3.
    destruct i as [|[|[|[|i]]]]; destruct j as [|[|[|[|j]]]];
      try lia; try discriminate; simpl in H4; lia.
  - intros H.
    discriminate H.
Qed.