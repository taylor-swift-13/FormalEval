Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.
Open Scope R_scope.

Definition derivative_spec (xs : list R) (result : list R) : Prop :=
  length result = pred (length xs) /\
  forall (i : nat), (i < length result)%nat ->
    nth i result 0 = (nth (S i) xs 0) * INR (S i).

Example test_derivative: derivative_spec 
  [3.6845190419876506; 6.8; -2.413995463147514; -39; 1.8861584708109862; 3.5; -2.8; 1.1; -4.4; -4.5; -5; 3.5; 0] 
  [6.8; -4.827990926295028; -117; 7.5446338832439448; 17.5; -16.8; 7.7; -35.2; -40.5; -50; 38.5; 0].
Proof.
  unfold derivative_spec.
  split.
  
  - simpl. reflexivity.
    
  - intros i H.
    simpl in H.
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    destruct i; [ simpl; lra | ].
    lia.
Qed.