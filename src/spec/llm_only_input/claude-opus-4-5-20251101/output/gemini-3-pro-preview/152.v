Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition compare_spec (game guess result : list Z) : Prop :=
  length game = length guess /\
  length result = length game /\
  (forall i : nat, (i < length game)%nat ->
    nth i result 0 = Z.abs (nth i game 0 - nth i guess 0)).

Example test_compare :
  compare_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z] [1%Z; 2%Z; 3%Z; 4%Z; 2%Z; -2%Z] [0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 3%Z].
Proof.
  unfold compare_spec.
  split.
  - simpl. reflexivity.
  - split.
    + simpl. reflexivity.
    + intros i Hi.
      simpl in Hi.
      destruct i as [|i'].
      * simpl. reflexivity.
      * destruct i' as [|i''].
        -- simpl. reflexivity.
        -- destruct i'' as [|i'''].
           ++ simpl. reflexivity.
           ++ destruct i''' as [|i''''].
              ** simpl. reflexivity.
              ** destruct i'''' as [|i'''''].
                 --- simpl. reflexivity.
                 --- destruct i''''' as [|i''''''].
                     +++ simpl. reflexivity.
                     +++ simpl in Hi. lia.
Qed.