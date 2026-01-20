Require Import List.
Require Import ZArith.
Require Import Lia.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example rolling_max_spec_case1 :
  rolling_max_spec [10%Z; 5%Z; 20%Z; 30%Z; 25%Z; 20%Z; 15%Z; 10%Z; 19%Z]
                   [10%Z; 10%Z; 20%Z; 30%Z; 30%Z; 30%Z; 30%Z; 30%Z; 30%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i]; simpl; try reflexivity.
    destruct i as [|i].
    + simpl. reflexivity.
    + simpl in Hi. exfalso. lia.
Qed.