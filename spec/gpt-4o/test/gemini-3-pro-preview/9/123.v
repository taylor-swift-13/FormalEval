Require Import List.
Require Import Arith.
Require Import Lia.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn ((i + 1)%nat) numbers) 0.

Example test_rolling_max : rolling_max_spec 
  [5; 10; -1; -5; 20; 15; 6; 9; -8; -1] 
  [5; 10; 10; 10; 20; 20; 20; 20; 20; 20].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    do 10 (destruct i; [simpl; reflexivity | ]).
    simpl in H.
    lia.
Qed.