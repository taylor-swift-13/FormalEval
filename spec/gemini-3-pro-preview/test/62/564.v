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
  [1; -5; -4; 0; 0; 2.5; 6.8; 9; 3.5; 2.5] 
  [-5; -8; 0; 0; 12.5; 40.8; 63; 28; 22.5].
Proof.
  unfold derivative_spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    (* We iterate through the specific indices 0 to 8 *)
    do 9 (destruct i; [ simpl; lra | ]).
    (* Case i >= 9 contradicts Hi (i < 9) *)
    lia.
Qed.