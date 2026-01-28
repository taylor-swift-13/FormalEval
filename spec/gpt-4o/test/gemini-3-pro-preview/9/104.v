Require Import List.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) (nth 0 numbers 0).

Example test_rolling_max_neg : 
  rolling_max_spec 
    [-10; -5; -3; -4; -8; -11; -15; -12; 0; 5] 
    [-10; -5; -3; -3; -3; -3; -3; -3; 0; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [
      vm_compute; reflexivity |
      simpl in H; try lia
    ]).
Qed.