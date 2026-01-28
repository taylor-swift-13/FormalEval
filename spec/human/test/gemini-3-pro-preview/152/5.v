Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0%Z = Z.abs (nth i game 0%Z - nth i guess 0%Z).

Example test_problem_152:
  problem_152_spec
    [1; 1; 1; 1; 1]
    [0; 0; 0; 0; 0]
    [1; 1; 1; 1; 1].
Proof.
  unfold problem_152_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      do 5 (destruct i; [ simpl; reflexivity | ]).
      simpl in Hi.
      lia.
Qed.