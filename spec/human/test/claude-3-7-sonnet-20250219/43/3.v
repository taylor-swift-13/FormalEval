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

Example test_problem_43 : problem_43_spec [1%Z; 2%Z; 3%Z; 7%Z] false.
Proof.
  unfold problem_43_spec.
  split.
  - intros [i [j [H1 [H2 [H3 H4]]]]].
    simpl in H2, H3.
    destruct i as [|[|[|[|i]]]]; destruct j as [|[|[|[|j]]]];
      try lia; try discriminate; simpl in H4.
    all: try (
      (* Check sums of pairs *)
      repeat match goal with
      | H: _ + _ = 0 |- _ => 
        (* Each sum case: 1+2=3,1+3=4,1+7=8,2+3=5,2+7=9,3+7=10, none zeros *)
        clear H; fail
      end; lia).
  - intros H.
    discriminate H.
Qed.