Require Import List.
Require Import Reals.
Require Import Psatz.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = (length xs - 1)%nat /\
  forall i : nat, (i < length result)%nat ->
    nth i result 0 = nth (S i) xs 0 * INR (S i).

Example test_derivative: derivative_spec 
  [3.5; -2.8; 1.1; -4.4; 0; 3.0619344202870824; 3.5; 3.5; -2.8] 
  [-2.8; 2.2; -13.2; 0; 15.309672101435412; 21.0; 24.5; -22.4].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    do 8 (destruct i as [|i]; [ simpl; lra | ]).
    lia.
Qed.