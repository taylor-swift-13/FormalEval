Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = 
            let prefix := firstn (S i) numbers in
            fold_left Z.max (tl prefix) (hd 0 prefix).

Example test_rolling_max_case1 : rolling_max_spec [-1; -2; -3; -4; -5; -4; -2; -1; 15; 2] [-1; -1; -1; -1; -1; -1; -1; -1; 15; 15].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.