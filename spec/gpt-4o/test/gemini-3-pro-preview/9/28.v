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
            | x :: xs => fold_left Z.max xs x
            end.

Example test_rolling_max_negatives : 
  rolling_max_spec 
    [-1; -2; -3; -4; -4; -3; -2; -1; -4] 
    [-1; -1; -1; -1; -1; -1; -1; -1; -1].
Proof.
  unfold rolling_max_spec.
  split.
  - reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; try reflexivity; try lia | simpl in H; try lia ]).
Qed.