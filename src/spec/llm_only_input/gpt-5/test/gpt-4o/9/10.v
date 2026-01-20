Require Import List.
Require Import ZArith.
Require Import Lia.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example rolling_max_spec_increasing :
  rolling_max_spec [10%Z; 20%Z; 30%Z; 40%Z; 50%Z]
                   [10%Z; 20%Z; 30%Z; 40%Z; 50%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi. simpl in Hi.
    destruct i as [|i]; simpl; [reflexivity|].
    destruct i as [|i]; simpl; [reflexivity|].
    destruct i as [|i]; simpl; [reflexivity|].
    destruct i as [|i]; simpl; [reflexivity|].
    destruct i as [|i]; simpl.
    + reflexivity.
    + exfalso. lia.
Qed.