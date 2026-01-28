Require Import List.
Require Import Reals.
Require Import Lra.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec 
  [1; -4; 0; 2.5; 6.8; 9; 10.2; 1.5; -4; 10.2; 10.2; 1.5; 10.2] 
  [-4; 0; 7.5; 27.2; 45; 61.2; 10.5; -32; 91.8; 102; 16.5; 122.4].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 12 (destruct i as [|i]; [simpl; lra | ]).
    lia.
Qed.