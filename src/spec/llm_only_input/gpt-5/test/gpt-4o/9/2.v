Require Import List.
Require Import ZArith.
Require Import Lia.

Import ListNotations.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, i < length numbers ->
            nth i result 0%Z = fold_left Z.max (firstn (i + 1) numbers) 0%Z.

Example rolling_max_spec_increasing : rolling_max_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 2%Z; 3%Z; 4%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    destruct i as [|i].
    + simpl. rewrite Z.max_r by lia. reflexivity.
    + destruct i as [|i].
      * simpl. repeat rewrite Z.max_r by lia. reflexivity.
      * destruct i as [|i].
        -- simpl. repeat rewrite Z.max_r by lia. reflexivity.
        -- destruct i as [|i].
           ++ simpl. repeat rewrite Z.max_r by lia. reflexivity.
           ++ simpl in Hi. lia.
Qed.