Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_152_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  forall i, (i < length game)%nat ->
    nth i result 0 = Z.abs (nth i game 0 - nth i guess 0).

Example test_compare_example :
  problem_152_spec
    [1; 2; 3; 4; 5; 1]
    [1; 2; 3; 4; 2; -2]
    [0; 0; 0; 0; 3; 3].
Proof.
  unfold problem_152_spec.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros i Hi.
      destruct i as [|i1].
      * simpl. reflexivity.
      * destruct i1 as [|i2].
        -- simpl. reflexivity.
        -- destruct i2 as [|i3].
           ++ simpl. reflexivity.
           ++ destruct i3 as [|i4].
              ** simpl. reflexivity.
              ** destruct i4 as [|i5].
                 --- simpl. reflexivity.
                 --- destruct i5 as [|i6].
                     +++ simpl. reflexivity.
                     +++ lia.
Qed.