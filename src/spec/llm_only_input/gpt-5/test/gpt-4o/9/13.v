Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example rolling_max_spec_example :
  rolling_max_spec
    [1%Z; 2%Z; 3%Z; 2%Z; 1%Z; 2%Z; 3%Z; 2%Z; 1%Z]
    [1%Z; 2%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z; 3%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi. simpl in Hi.
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i]; [simpl; reflexivity |].
    destruct i as [|i].
    + simpl. reflexivity.
    + exfalso. lia.
Qed.