Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (S i) numbers) (nth 0%nat numbers 0).

Example test_rolling_max_case1 : rolling_max_spec 
  [-1; -2; -3; 2; -3; -4; -3; -2; -1; -2; -3; -4; -5; -4; -3; -2; -1; 0; -1; -2; -3; -2; 0; 1; 0; -1; -2]
  [-1; -1; -1; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.