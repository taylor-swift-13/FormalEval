Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

Definition problem_152_pre (game guess : list Z) : Prop := length game = length guess.

Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0%Z = Z.abs (nth i game 0%Z - nth i guess 0%Z).

Example problem_152_test_1 :
  problem_152_spec
    [10%Z; 30%Z; 39%Z; 50%Z; 50%Z; 39%Z]
    [10%Z; 30%Z; 39%Z; 50%Z; 50%Z; 39%Z]
    [0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z].
Proof.
  unfold problem_152_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      destruct i as [|i1].
      * simpl. reflexivity.
      * destruct i1 as [|i2].
        { simpl. reflexivity. }
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        destruct i3 as [|i4].
        { simpl. reflexivity. }
        destruct i4 as [|i5].
        { simpl. reflexivity. }
        destruct i5 as [|i6].
        { simpl. reflexivity. }
        exfalso. simpl in Hi. lia.
Qed.