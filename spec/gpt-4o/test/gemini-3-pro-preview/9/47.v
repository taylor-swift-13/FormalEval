Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = 
            match firstn (i + 1)%nat numbers with
            | [] => 0
            | h :: t => fold_left Z.max t h
            end.

Example test_rolling_max_mixed : 
  rolling_max_spec [0; 4; -3; -4; -5; -3; 15; -1; 2] 
                   [0; 4; 4; 4; 4; 4; 15; 15; 15].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 9 (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.