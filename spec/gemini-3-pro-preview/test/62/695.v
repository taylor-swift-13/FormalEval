Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (result : list Z) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * Z.of_nat (S i).

Example test_derivative: derivative_spec 
  [3; -25; -40; 0; 5; 63; 0; 10; 62; 0; 11] 
  [-25; -80; 0; 20; 315; 0; 70; 496; 0; 110].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    (* Verify element-wise calculation for indices 0 to 9 *)
    do 10 (destruct i as [|i]; [ vm_compute; reflexivity | ]).
    (* For i >= 10, the hypothesis H (i < 10) is contradictory *)
    lia.
Qed.