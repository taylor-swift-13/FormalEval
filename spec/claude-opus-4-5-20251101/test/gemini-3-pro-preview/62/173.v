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
  [1.5; 1; -2; 0; 3.4009590491925366; -5; 0; 1.2; 0; -4.5; 0; 2] 
  [1; -4; 0; 13.6038361967701464; -25; 0; 8.4; 0; -40.5; 0; 22].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 11 (destruct i as [|i]; [ simpl; lra | ]).
    lia.
Qed.