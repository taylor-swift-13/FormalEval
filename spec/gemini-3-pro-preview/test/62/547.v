Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec [1; -1; 0; 0; 0; 0; -24; 1; 0; 0; -7; 0; 0; 1] [-1; 0; 0; 0; 0; -144; 7; 0; 0; -70; 0; 0; 13].
Proof.
  unfold derivative_spec.
  split.
  - reflexivity.
  - intros i H.
    (* We verify the condition for each index 0 to 12 using 'do 13' *)
    do 13 (destruct i; [ vm_compute; reflexivity | ]).
    (* For i >= 13, the hypothesis H (i < 13) is contradictory *)
    simpl in H. lia.
Qed.