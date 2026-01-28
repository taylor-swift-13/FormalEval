Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i : nat, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) 0.

Example test_rolling_max : rolling_max_spec [0; 4; -3; -4; -5; -4; -3; -2; -1; 2] [0; 4; 4; 4; 4; 4; 4; 4; 4; 4].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.