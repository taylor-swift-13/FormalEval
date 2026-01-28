Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length numbers = length result /\
  forall i, (i < length numbers)%nat ->
            nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) 0.

Example test_rolling_max_complex : rolling_max_spec 
  [5; -11; 4; 6; 4; 7; 10; 3; 8; 2; 4; 6; 6; 6; 5; 10]
  [5; 5; 5; 6; 6; 7; 10; 10; 10; 10; 10; 10; 10; 10; 10; 10].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    simpl in H. lia.
Qed.