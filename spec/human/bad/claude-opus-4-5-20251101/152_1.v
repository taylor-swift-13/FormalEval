Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0 = Z.abs (nth i game 0 - nth i guess 0).

Example problem_152_test1 :
  problem_152_spec [1; 2; 3; 4; 5; 1] [1; 2; 3; 4; 2; (-2)] [0; 0; 0; 0; 3; 3].
Proof.
  unfold problem_152_spec.
  split; [reflexivity|].
  split; [reflexivity|].
  intros i Hi.
  do 6 (destruct i; [simpl; reflexivity|]).
  simpl in Hi. lia.
Qed.