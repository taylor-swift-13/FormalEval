Require Import List.
Require Import Lia.
Require Import ZArith.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (S i) numbers) 0%Z.

Example rolling_max_spec_case : rolling_max_spec [4%Z; 3%Z; 1%Z; 1%Z; 1%Z] [4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i1].
    + simpl. reflexivity.
    + destruct i1 as [|i2].
      * simpl. reflexivity.
      * destruct i2 as [|i3].
        { simpl. reflexivity. }
        { destruct i3 as [|i4].
          - simpl. reflexivity.
          - destruct i4 as [|i5].
            + simpl. reflexivity.
            + simpl in Hi. lia.
        }
Qed.